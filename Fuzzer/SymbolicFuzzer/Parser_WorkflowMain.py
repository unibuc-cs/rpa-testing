import json
import sys
import pickle
import os
from Parser_WorkflowExpressions import *
from Executor_NodesExec import *
import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph

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


class NodeTypes(Enum):
    BASE_NODE = 0 # Abstract, base
    FLOW_NODE = 1 # Normal node for flow, no branching
    BRANCH_NODE = 2 # Branch node

def extractVarNameFromVarPlain(varNamePlain):
    """
    Expecting a "V['name']" => name
    """
    assert varNamePlain[0] == 'V' and varNamePlain[1] == '[' and varNamePlain[-1] == "]"
    subtactVar = varNamePlain[3:-2]
    subtactVar = subtactVar.replace('\\', "")
    return subtactVar

class BaseSymGraphNode():
    def __init__(self, id : str, nodeType : NodeTypes):
        self.id = id
        self.nodeType : NodeTypes = nodeType

        # This is the node available for executor
        self.fuzzerNodeInst = ASTFuzzerNode()

    def __str__(self):
        return self.id #+ " " + str(self.expression)

    def isBranchNode(self) -> bool:
        return False

    def getGraphNameFromNodeId(self) -> str:
        index = self.id.find(':')
        assert index != -1, "There is no namespace for this node !"
        return str(self.id[:index])

    # Gets a debug label string to be used for this node
    def getDebugLabel(self):
        # HTML way ...maybe later
        # labelStr = f"<{nodeInst.id}<BR/><FONT POINT-SIZE=\"10\">v[add]  &gt 100 </FONT>>"

        baseOutput = self.id

        # TODO: more stuff into the new output
        """
        if self.hasAssignments():
            for assignment in self.assignments:
                baseOutput += "\n" + str(assignment.leftTerm) + " <- " + str(assignment.rightTerm)
        """
        return baseOutput

class SymGraphNodeFlow(BaseSymGraphNode):
    def __init__(self, id : str):
        super().__init__(id, NodeTypes.FLOW_NODE)
        self.nextNodeId : str = None


# A generic branch node definition
class SymGraphNodeBranch(BaseSymGraphNode):  # Just an example of a base class
    def __init__(self, id : str, condition : str):
        super().__init__(id, NodeTypes.BRANCH_NODE)
        self.expression = condition
        self.valuesAndNext : Dict[str, str] = {} # A dictionary from expression value to next branch

    def getVariables(self):
        return None # self.expression.variables()

    def isBranchNode(self) -> bool:
        return True

    def getDebugLabel(self):
        baseOutput = super().getDebugLabel()
        outputStr = baseOutput + "\n" + str(self.expression)
        return outputStr

    """
    # Functions and examples to inspect the graph at a higher level
    #-------------------------------------------------
    # A function to collect all variables by nodes
    def getAllVariables(self) -> set:
        setOfVariables = set()
        for node in self.graph.nodes:
            node = fixNodeInstance(graph, node)
            variablesInNode = node.getVariables()
            setOfVariables.update(variablesInNode)
        return setOfVariables
    """

class WorkflowGraph:
    def __init__(self):
        # Data needed and filled in when parsing the workflows
        self.entryTestNodeId = None
        self.debugColors = None
        self.mainWorkflowName = None

        # This is the connection to the nx digraph instance
        self.graph = nx.DiGraph()
        self.graph.clear()

    def setMainWorkflowName(self, name : str):
        self.mainWorkflowName = name
        self.graph['graphName'] = name

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

    def parseWorkflows(self, inputPath : str, baseOutPath : str) -> WorkflowGraph:
        workflowGraph : WorkflowGraph = WorkflowGraph()

        with open(inputPath) as json_file:
            dataAll = json.load(json_file)

            workflowsDataSpec = dataAll['workflows']
            graph = dataAll['graph']
            startNode = dataAll['startNode']
            startGraph = startNode.split(":")
            assert len(startGraph) > 0
            workflowGraph.setMainWorkflowName(startGraph[0])
            workflowGraph.entryTestNodeId = startNode

            debugColors = {}
            nodeIdToInstance: Dict[str, SymGraphNodeBranch] = {}

            # Step 0: Create the variables, check all existing workflows, create debug colors and append to the variables dictionary each individual workflow used
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
            out_path = os.path.join(baseOutPath, OUTPUT_FILE_NAME)


            # Step 1: Create all the node firsts and cache the inverse dictionary in the graph from node_id to node instance
            for nodeFullName, nodeData in graph.items():
                nodeFullNameSplit = nodeFullName.split(":")
                assert len(nodeFullNameSplit) ==2, f"Node content is {nodeFullNameSplit}. Expecting format namespace:nodeName"
                parentGraphName = nodeFullNameSplit[0]
                nodeName = nodeFullNameSplit[1]

                # Parse node expr
                expression_raw_str = nodeData.get('expression_raw_str')
                expression_node = None
                if expression_raw_str != "" and expression_raw_str != None:
                    expression_node = self.workflowExpressionParser.parseModuleCodeBlock(expression_raw_str)
                    assert len(expression_node) == 1, " Currently we expected 1 understandable code block in the input. Do you need more or less ?"
                    expression_node = expression_node[0]

                # Create a node based on its expression node
                nodeInst = None
                if not expression_node.type == ASTFuzzerNodeType.COMPARATOR:
                    nodeInst = SymGraphNodeFlow(id=nodeFullName)
                else:
                    nodeInst = SymGraphNodeBranch(id=nodeFullName)
                nodeInst.expression = expression_node

                # Register the new node in the local map
                nodeIdToInstance[nodeFullName] = nodeInst

                # Fill in the debug info stuff for this node
                # See here all the graphiviz attributes: https://graphviz.org/doc/info/attrs.html
                node_shape = None
                if nodeInst.id == self.entryTestNodeId:
                    node_shape = 'doubleoctagon'
                elif nodeInst.nodeType == NodeTypes.BRANCH_NODE:
                    node_shape = 'diamond'
                else:
                    node_shape = 'box'

                # 'square' if nodeInst.nodeType == NodeTypes.BranchNode else 'circle'
                nodeGraphParentName = nodeInst.getGraphNameFromNodeId()
                assert nodeGraphParentName in workflowGraph.debugColors, f"Looking for graph named {nodeGraphParentName} but it doesn't exist "
                node_color = workflowGraph.debugColors[nodeGraphParentName]
                node_fill_color = 'blue' if nodeInst.id == workflowGraph.entryTestNodeId else 'white'
                node_style = 'filled'

                labelStr = nodeInst.getDebugLabel()

                # HTML way ...maybe later
                # labelStr = f"<{nodeInst.id}<BR/><FONT POINT-SIZE=\"10\">v[add]  $#60 100 </FONT>>"

                # TODO: refactor below

                # Deal with transitions
                transitions = nodeData.get('transitions')


                # 'square' if nodeInst.nodeType == NodeTypes.BranchNode else 'circle'
                nodeGraphParentName = nodeInst.getGraphNameFromNodeId()
                assert nodeGraphParentName in self.debugColors, f"Looking for graph named {nodeGraphParentName} but it doesn't exist "
                node_color = self.debugColors[nodeGraphParentName]
                node_fill_color = 'blue' if nodeInst.id == self.entryTestNodeId else 'white'
                node_style = 'filled'

                labelStr = nodeInst.getDebugLabel()

                # HTML way ...maybe later
                # labelStr = f"<{nodeInst.id}<BR/><FONT POINT-SIZE=\"10\">v[add]  $#60 100 </FONT>>"

                graph.add_node(nodeInst, label=labelStr, shape=node_shape, color=node_color, fillcolor=node_fill_color,
                               style=node_style)

            graph.graph['nodeIdToInstance'] = nodeIdToInstance

            # Step 2: Create the links inside the nodes and graph
            for nodeId, nodeSpec in dictSpec.items():
                parentNodeInst = nodeIdToInstance[nodeId]

                if parentNodeInst.nodeType == NodeTypes.BRANCH_NODE:

                    # Solve successors for each condition
                    nodeSuccessorsSpec = nodeSpec[1]
                    assert isinstance(nodeSuccessorsSpec, list), f"Expecting a list here for node successors desc!"
                    for nodeSucc in nodeSuccessorsSpec:
                        nextNodeVal = nodeSucc[0]
                        nextNodeId = nodeSucc[1]

                        succNodeInst = nodeIdToInstance[nextNodeId]
                        parentNodeInst.valuesAndNext[nextNodeVal] = nextNodeId

                        edgeLabel: str = 'T' if nextNodeVal == 'True' else 'F'
                        graph.add_edge(parentNodeInst, succNodeInst, label=edgeLabel, labelfontsize=20)
                elif parentNodeInst.nodeType == NodeTypes.FLOW_NODE:
                    assert nodeSpec[0] == None

                    # Solve successor
                    successor = nodeSpec[1]
                    assert successor is None or isinstance(successor, str)
                    parentNodeInst.nextNodeId = successor

                    if successor != None:
                        succNodeInst = nodeIdToInstance[successor]
                        graph.add_edge(parentNodeInst, succNodeInst)

            return graph

        return workflowGraph

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
