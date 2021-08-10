import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph
from enum import Enum
from Executor_NodesExec import *
import json
import  csv

# Logic to get a debug color output depending on the name of the graph
AllDebugColors = ["red", "blue", "yellow", "green", "violet", "orange"]
NumDebugColors = len(AllDebugColors)
def getDebugColorByName(name : str) -> str:
    return AllDebugColors[(hash(name) % NumDebugColors)]

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
        self.fuzzerNodeInst = None

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

    def getDebugLabel(self):
        baseOutput = super().getDebugLabel()
        outputStr = baseOutput\

        if self.expression is not None:
            if isinstance(self.expression, (ASTFuzzerNode_Assignment)):
                outputStr += "\n" + str(self.expression)
        return outputStr


# A generic branch node definition
class SymGraphNodeBranch(BaseSymGraphNode):  # Just an example of a base class
    def __init__(self, id : str):
        super().__init__(id, NodeTypes.BRANCH_NODE)
        self.expression_rawStr : str = None # The string raw expression as defined in the config file
        self.expression : ASTFuzzerNode = None # The parsed node expression of above
        self.valuesAndNext : Dict[str, str] = {} # A dictionary from expression value to next branch

    def getVariables(self):
        return None # self.expression.variables()

    def isBranchNode(self) -> bool:
        return True

    def getDebugLabel(self):
        baseOutput = super().getDebugLabel()
        outputStr = baseOutput + "\n" + str(self.expression)
        return outputStr

class WorkflowGraph:
    def __init__(self, dataStore, astFuzzerNodeExecutor):
        # Data needed and filled in when parsing the workflows
        self.entryTestNodeId = None
        self.debugColors = None
        self.mainWorkflowName = None
        self.DS : DataStore = dataStore
        self.astFuzzerNodeExecutor = astFuzzerNodeExecutor

        # This is the connection to the nx digraph instance
        self.graphInst = nx.DiGraph()
        self.graphInst.clear()

    def setMainWorkflowName(self, name : str):
        self.mainWorkflowName = name
        self.graphInst.graph['graphName'] = name

    # A function to collect all paths in the graph. For loops it just consider one iteration case as long as every branch is covered
    # For infinite graphs we'll consider IDA approach
    def __getAllPaths(self):
        # We are now getting a parameter for the entry node for testing so the code below is not used anymore
        if False:
            # Get all the starting nodes (in degree = 0)
            start_nodes = []
            for node in self.mainGraph.nodes:
                node = self.__fixNodeInstance(node)
                if self.mainGraph.in_degree[node] == 0:
                    start_nodes.append(node)
        else:
            nodeIdsToInstances = self.graphInst.graph['nodeIdToInstance']

            # Test 1: is the entry test node given in the graph at least ?:)
            start_nodes = [nodeIdsToInstances[self.entryTestNodeId]]

        # print(start_nodes[0].name)
        allpaths = []
        def _findpath(graph, currNode, currPath, visitedNodes : Set[any], outAllPaths):
            currPath.append(currNode)
            visitedNodes.add(currNode.id)

            if graph.out_degree[currNode] == 0:  # leaf node ?
                outAllPaths.append(currPath)
            else:
                any_successor = False # It might happen that no successor to be valid because of the unique nodes on paths condition.

                # For each successor add this node to a copy of the list and iterate on that path
                for succNode in graph.successors(currNode):
                    succNode = self.__fixNodeInstance(succNode)

                    if succNode.id in visitedNodes:
                        continue

                    any_successor = True

                    newCurrPath = copy.deepcopy(currPath)
                    newVisitedNodes = copy.deepcopy(visitedNodes)
                    _findpath(graph, succNode, newCurrPath, newVisitedNodes, outAllPaths)

                if any_successor is False:
                    outAllPaths.append(currPath) # New path then !

        # From each starting node, run a directed search path until leafs
        for snode in start_nodes:
            _findpath(graph=self.graphInst, currNode=snode,
                      currPath=[], visitedNodes=set(), outAllPaths=allpaths)

        return allpaths

    # A function to fix the node finding inside a graph
    def __fixNodeInstance(self, node):
        if isinstance(node, str):
            nodeIdToInstance = self.graphInst.graph['nodeIdToInstance']
            node = nodeIdToInstance[node]
        return node

    def __debugPrintSinglePath(self, path):
        pathStr = ""
        for node in path:
            node = self.__fixNodeInstance(node)
            pathStr += str(node.id) + " ; "
        return pathStr

    def __debugPrintPaths(self, paths):
        for index, P in enumerate(paths):
            print("--- Path ", index, ": ")
            pathStr = self.__debugPrintSinglePath(P)
            print(pathStr)

    def __debugInspectGraph(self):
        print("Graph nodes: ")
        for node in self.graphInst.nodes:
            print(node)

        print("Graph edges: ")
        for edge in self.graphInst.edges:
            start = edge[0]
            end = edge[1]
            print(f"start from {start.id} end {end.id}")

        print("In Degrees: ", self.graphInst.in_degree([node for node in self.graphInst.nodes]))
        print("Out Degrees: ", self.graphInst.out_degree([node for node in self.graphInst.nodes]))

    # Debugging the graph...
    def debugGraph(self, outputGraphFile=None):
        print("Drawing and showing the graph")
        # nx.draw_networkx(self.graph)
        # plt.pyplot.show()
        A = to_agraph(self.graphInst)
        A.layout('dot')
        A.draw(outputGraphFile)

        # Let's inspect the graph...
        self.__debugInspectGraph()

        print("Checking all paths inside the graph !")
        allpaths = self.__getAllPaths()
        self.__debugPrintPaths(allpaths)

        print("\n\nGetting all used variables inside branches ")
        print("== Symbolic variables: \n", self.DS.SymbolicValues.keys())  # print(getAllVariables(graph))
        print("== All variables: \n", self.DS.Values.keys())  # print(getAllVariables(graph))

    # TODO: the two functions below need to be refactored !!
    def __getPathConditions(self, path):
        assert isinstance(path, list) and len(path) > 0 #and isinstance(path[0], SymGraphNodeBranch)
        pathLen = len(path)
        outCOnditions = []
        for nodeIndex in range(pathLen):
            currNode : BaseSymGraphNode = path[nodeIndex]

            # Add the condition for a branching node
            if currNode.nodeType == NodeTypes.BRANCH_NODE:
                nextNode = path[nodeIndex + 1] if (nodeIndex + 1 < pathLen) and len(currNode.valuesAndNext) > 0 else None

                symbolicExpressionForNode = self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(currNode.expression)

                # DEBUG CODE
                if "actual_pin" in symbolicExpressionForNode:
                    a = 3
                    a +=1
                    symbolicExpressionForNode = self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(currNode.expression)

                # Fix the condition to solve
                condToSolve = symbolicExpressionForNode
                if nextNode != None and condToSolve != None:
                    # Is inverse branch for next node ?
                    if 'False' in currNode.valuesAndNext and currNode.valuesAndNext['False'] == nextNode.id:
                        condToSolve = 'Not(' + condToSolve + ')'
                    else:
                        assert currNode.valuesAndNext['True'] == nextNode.id

                    outCOnditions.append(condToSolve)
            else:
                if currNode.expression:
                    self.astFuzzerNodeExecutor.executeNode(currNode.expression)

            # Add the conditions for assignment variables
            """
            if currNode.hasAssignments():
                for assignmentInst in currNode.assignments:
                    assert isinstance(assignmentInst, AssignmentOperation)
                    if assignmentInst.isOverridingValueAssignment:
                        continue # Ignored for now. TODO: Ciprian !

                    targetVar = assignmentInst.leftTerm
                    targetValue = assignmentInst.rightTerm
                    outCOnditions.append(f"{targetVar}=={targetValue}")
            """

        return outCOnditions

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solveOfflineStaticGraph(self, outputCsvFile=None, debugLogging=False, astFuzzerNodeExecutor=None):
        fieldNamesList = [key for key in self.DS.Values.keys()]
        if debugLogging:
            fieldNamesList.append("GraphPath")
        set_fieldNamesList = set(fieldNamesList)

        csv_stream = None
        if outputCsvFile != None:
            csv_file = open(outputCsvFile, mode='w')
            csv_stream = csv.DictWriter(csv_file, delimiter=',', quotechar='"', quoting=csv.QUOTE_MINIMAL, fieldnames=fieldNamesList)
            csv_stream.writeheader()

        #condA = 'V["loan"] < 1000' # Just a dummy test to evaluate a simple condition...
        #eval(condA)
        allpaths = self.__getAllPaths()

        for index, P in enumerate(allpaths):
            pathStr = None
            if debugLogging:
                pathStr = self.__debugPrintSinglePath(P)
                print(f"Analyzing path {index}: [{pathStr}]")
                print("-------------------------")
            conditions_str = self.__getPathConditions(allpaths[index])

            conditions_z3 = []
            for s in conditions_str:
                #print(f"Current condition {s} ...")
                cond = eval(s)
                conditions_z3.append(cond)

            solver = Solver()
            # Add all the required conditions for the constant variables
            #for constName, constValue in self.V_constants.items():
            #    solver.add(self.V[constName] == constValue)

            # Add all the required conditions for the path
            for cond_z3 in conditions_z3:
                solver.add(cond_z3)

            isSolution = solver.check()
            # print(isSolution)
            if isSolution and isSolution != z3.unsat:
                if debugLogging:
                    print("Found a solution")
                m = solver.model()

                # Print debug all declarations
                for d in m.decls():
                    if debugLogging:
                        print(f"{d.name()}={m[d]}")

                # Get one output row for csv extract
                if csv_stream != None:
                    rowContent = {}
                    # For each variabile in the model, output its storage
                    for decl in m.decls():
                        declAsString = str(decl)
                        if declAsString in set_fieldNamesList:
                            valueOfDecl = m[decl]
                            if z3.is_int_value(valueOfDecl):
                                valueOfDecl = valueOfDecl.as_long()
                            elif z3.is_real(valueOfDecl):
                                valueOfDecl = float(valueOfDecl.as_decimal(prec=2))

                            elif z3.is_bool(valueOfDecl):
                                valueOfDecl = True if z3.is_true(valueOfDecl) else False

                            rowContent[declAsString] = valueOfDecl
                    if pathStr != None:
                        rowContent["GraphPath"] =pathStr

                    if csv_stream:
                        csv_stream.writerow(rowContent)
            else:
                if debugLogging:
                    print("No solution exists for this path")


