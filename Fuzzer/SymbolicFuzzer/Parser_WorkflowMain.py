import json
import sys
import pickle
import os
from Parser_WorkflowExpressions import *
from Executor_NodesExec import *


OUTPUT_FILE_NAME = "_tempExpressionParser.txt" # The name output obtained after running the script on the given input


AllDebugColors = ["red", "blue", "yellow", "green", "violet", "orange"]
NumDebugColors = len(AllDebugColors)
def getDebugColorByName(name : str) -> str:
    return AllDebugColors[(hash(name) % NumDebugColors)]


"""
def ast_to_string(localast, rname):
    # AST to string - using preorder
    # to change for ternary operations
    if localast.token_type == myparser.TokenType.T_VAR:
        # localstr = 'V['+ localast.value+']'
        localstr = 'V[\'' + rname + ':' + localast.value + '\']'
    else:
        localstr = localast.value
    st = ''
    dr = ''
    if len(localast.children) > 0:

        if len(localast.children[0].children) == 0:
            st = str(ast_to_string(localast.children[0], rname))
        else:
            st = "(" + str(ast_to_string(localast.children[0], rname)) + ")"
        if len(localast.children) == 2:
            if len(localast.children[1].children) == 0:
                dr = str(ast_to_string(localast.children[1], rname))
            else:
                dr = "(" + str(ast_to_string(localast.children[1], rname)) + ")"

    if st == '' and dr == '':
        localstr = localstr
    elif st == '' and dr != '':
        localstr = localstr + ' ' + dr
    elif st != '' and dr == '':
        localstr = localstr + ' ' + st
    elif localast.value in ["And", 'Or']:
        localstr = localstr + '(' + st + ',' + dr + ')'
    else:
        localstr = st + ' ' + localstr + ' ' + dr
    return localstr
"""


class WorkflowParser:
    def __init__(self, astFuzzerNodeExecutor : ASTFuzzerNodeExecutor,
                        workflowExpressionParser : WorkflowExpressionsParser):
        self.astFuzzerNodeExecutor = astFuzzerNodeExecutor
        self.workflowExpressionParser = workflowExpressionParser

    def parseVariable(self, workflowName : str, varName : str, varData):

        varType = varData["Type"]
        defaultValue = varData.get("Default")

        # Declare a variable and execute it in the executor
        # This will also put it in the datastore inside executor and make all connection links
        varDecl = ASTFuzzerNode_VariableDecl(varName=workflowName+ ":"+varName, typeName=varType, defaultValue=defaultValue)
        self.astFuzzerNodeExecutor.executeNode(varDecl)

    def parseWorkflows(self, inputPath : str, baseOutPath : str):
        with open(inputPath) as json_file:
            dataAll = json.load(json_file)

            workflowsDataSpec = dataAll['workflows']
            graph = dataAll['graph']
            startNode = dataAll['startNode']
            startGraph = startNode.split(":")
            assert len(startGraph) > 0
            mainWorkflowName = startGraph[0]

            z3Graph = {}
            debugColors = {}

            # Create debug colors and append to the variables dictionary each individual workflow used
            for workflowData in workflowsDataSpec:
                variables = workflowData['variables']
                graphName = workflowData['displayName']
                invokedBy = workflowData["invokedBy"]

                startNode = workflowData["startNode"]
                debugColors[graphName] = getDebugColorByName(graphName)

                # Parse each variable
                for varName, varData in variables.items():
                    self.parseVariable(workflowName = graphName, varName=varName, varData=varData)

            # Where to write the output
            out_path = os.path.join(baseOutPath, OUTPUT_FILE_NAME) #mainWorkflowName)

            # Parse the entire graph and save it in a file
            for nodeFullName, nodeData in graph.items():
                nodeFullNameSplit = nodeFullName.split(":")
                assert len(nodeFullNameSplit) ==2, f"Node content is {nodeFullNameSplit}. Expecting format namespace:nodeName"
                parentGraphName = nodeFullNameSplit[0]
                nodeName = nodeFullNameSplit[1]

                # Parse node expr
                expression = nodeData.get('expression')


                # Deal with transitions
                transitions = nodeData.get('transitions')



if __name__ == '__main__':
    # Get input
    inputPath = os.path.join('../Models', sys.argv[1])
    assert os.path.exists(inputPath), "File not found !"
    x = inputPath.rfind("/")
    y = inputPath[:(x - len(inputPath) + 1)]
    assert y != None and len(y) >= 0, "output path not defined"
    outputPath = y
    assert os.path.exists(outputPath), "output path was not found"

    # Create Workflow parser
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    workflowExpressionParser = WorkflowExpressionsParser()

    WP = WorkflowParser(astFuzzerNodeExecutor, workflowExpressionParser)
    WP.parseWorkflows(inputPath=inputPath, baseOutPath=outputPath)
