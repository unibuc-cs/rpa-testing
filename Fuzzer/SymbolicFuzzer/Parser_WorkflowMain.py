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
        varDecl = ASTFuzzerNode_VariableDecl(varName=varName, typeName=varType, defaultValue=defaultValue)
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

            if False:
                # Parse the entire graph and save it in a file
                for nodeFullName, nodeData in graph.items():
                    nodeFullNameSplit = nodeFullName.split(":")
                    assert len(nodeFullNameSplit) ==2, f"Node content is {nodeFullNameSplit}. Expecting format namespace:nodeName"
                    parentGraphName = nodeFullNameSplit[0]
                    nodeName = nodeFullNameSplit[1]


                    # the guard will contain the expression parsed using myparser
                    if nodeData['expression'] == '':
                        guard = 'None'
                    else:
                        ast = myparser.parse(nodeData['expression'])
                        guard = "\"" + ast_to_string(ast, parentGraphName) + "\""

                    # assigments
                    assign_list = nodeData.get("variableAssignments")
                    assignments = []
                    if assign_list:
                       assignment_var = assign_list['to']
                       assignment_exp = assign_list['value']
                       ast_v = myparser.parse(assignment_var)
                       ast_e = myparser.parse(assignment_exp)
                       if ast_e.token_type == myparser.TokenType.T_VAR:
                            ast_e_str = ast_to_string(ast_e, parentGraphName)
                       else:
                           ast_e_str =  ast_to_string(ast_e, parentGraphName)
                       assignments.append((ast_to_string(ast_v, parentGraphName), ast_e_str))

                    #invoked wf args
                    invokedWorkflow = nodeData.get("invokedWorkflow")
                    if invokedWorkflow:
                        variableMappings = nodeData["variableMappings"]
                        invokedWorkflowDisplayName = nodeData.get("invokedWorkflowDisplayName")
                        print(invokedWorkflowDisplayName)
                        if invokedWorkflowDisplayName == None:
                            invokedWorkflowDisplayName="Wf2"
                        for var in variableMappings:
                            type = var['argumentType']
                            v1_ast = myparser.parse(var['destinationWfArg'])
                            v2_ast = myparser.parse(var['sourceWfValue'])
                            if type=="Out":
                                asgn = (ast_to_string(v2_ast,parentGraphName),ast_to_string(v1_ast,invokedWorkflowDisplayName))
                            else:
                                asgn = (ast_to_string(v1_ast, invokedWorkflowDisplayName), ast_to_string(v2_ast, parentGraphName))
                            assignments.append(asgn)
                    # transitions contain a list of transitions
                    transitions = []
                    for trans in nodeData['transitions']:
                        transition = (trans['value'], trans['destination'])
                        # transition = (trans['value'],rname+':'+trans['destination'])
                        transitions.append(transition)
                    if len(transitions) == 0:
                        z3Graph[nodeFullName] = "(" + guard + "," + 'None' + ", "+str(assignments)+")"
                    elif len(transitions) == 1:
                        z3Graph[nodeFullName] = "(" + guard + ", \"" + str(transitions[0][1]) + "\", "+str(assignments)+")"

                    elif len(transitions) == 2:
                        z3Graph[nodeFullName] = "(" + guard + "," + "[" + str(transitions[0]) + "," + str(
                            transitions[1]) + "], " +str(assignments)+")"


                print(z3Vars)
                print(z3Graph)
                z3GraphStr = ""
                for (k, v) in z3Graph.items():
                    z3GraphStr = z3GraphStr + "\"" + k + "\"" + ": " + v + ",\n"
                z3GraphStr = z3GraphStr[:-2]
                data = "{" + "\"variables\"" + ": " + str(z3Vars) + ",\n" + \
                       "\"graph\": { \n" + z3GraphStr + "},\n " + \
                       '\"debugColors\": \"' + str(debugColors) + "\",\n " + \
                        "\"startNode\": " + "\"" + startNode + "\",\n " + \
                       "\"mainWorkflowName\": \"" + mainWorkflowName + "\" }" + "\n"

                text_file = open(out_path, "w")
                text_file.write(data)
                text_file.close()

            # return z3Graph

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
