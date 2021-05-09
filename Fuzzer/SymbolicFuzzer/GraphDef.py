
from py_expression_eval import Parser # Not used at the moment but might be good !
parser = Parser()
import copy
import csv
import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph
import pygraphviz as pgv
from typing import Dict, List, Set, Tuple
from z3 import *
import matplotlib as plt
from enum import Enum

class NodeTypes(Enum):
    BASE_NODE = 0 # Abstract, base
    FLOW_NODE = 1 # Normal node for flow, no branching
    BRANCH_NODE = 2 # Branch node

class BaseNode():
    def __init__(self, id : str, nodeType : NodeTypes):
        self.id = id
        self.nodeType : NodeTypes = nodeType

    def __str__(self):
        return self.id #+ " " + str(self.expression)

    def isBranchNode(self) -> bool:
        return False

    def getGraphNameFromNodeId(self) -> str:
        index = self.id.find(':')
        assert index != -1, "There is no namespace for this node !"
        return str(self.id[:index])

class FlowNode(BaseNode):
    def __init__(self, id : str):
        super().__init__(id, NodeTypes.FLOW_NODE)
        self.nextNodeId : str = None


# A generic branch node definition
class BranchNode(BaseNode):  # Just an example of a base class
    def __init__(self, id : str, condition : str):
        super().__init__(id, NodeTypes.BRANCH_NODE)
        self.expression = condition
        self.valuesAndNext : Dict[str, str] = {} # A dictionary from expression value to next branch

    def getVariables(self):
        return None # self.expression.variables()

    def isBranchNode(self) -> bool:
        return True

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



# Class for defining an workflow graph
class WorkflowDef:
    def __init__(self, variables : Dict[str, tuple or str], graph : Dict[any, any], name, color):
        self.variables = variables
        self.graph = graph
        self.name = name
        self.color = color


# Give all workflows, the main graph workflow name  and the entry point where you want your test to start from
# NOTE: the workflows should be given in the inverse order of priority ! They will override links
class SymbolicWorflowsTester():
    def __init__(self, workflows:List[WorkflowDef], mainWorflowName:str, entryTestNodeId:str):
        # Not used anymore
        """
        # Preprocessing the input to have the main graph first
        mainGraphDef = [w for w in workflows if w.name == mainWorflowName]
        assert len(mainGraphDef) == 1 , "The main graph is not in the given list, or present too many times"
        workflows = [w for w in workflows if w.name != mainWorflowName]
        workflows.insert(0, mainGraphDef[0])
        """

        self.entryTestNodeId = entryTestNodeId

        self.mainGraph = None # Symbolic graph structure
        self.allGraphs = []
        self.V = {} # Variables dict
        self.V_constants = {} # Context variables that are given as fixed for the model

        # Merge everything into a single graph and variables def
        graphVariables = {}
        graphDict = {}
        self.graphColors = {}
        for W in workflows:
            graphVariables.update(W.variables)
            graphDict.update(W.graph)
            self.graphColors[W.name] = W.color

        # Create the variables dictionary inside self.V
        self.__createVariables(graphVariables)

        # Create the symbolic graph
        self.mainGraph = self.__createTestGraph_fromDict(graphDict, mainWorflowName)

        self.do_checks()

    # This function performs different sanity checks to check the inputs such that we don't loose to much debugging time with wrong input..add here things like that
    def do_checks(self):
        nodeIdsToInstances = self.mainGraph.graph['nodeIdToInstance']

        # Test 1: is entry test node given in the graph at least ?:)
        assert nodeIdsToInstances[self.entryTestNodeId] is not None



    # A factory of variables by name and specification!
    def __createSingleVariableBySpec(self, varName, varSpec):
        varType = varSpec
        if not isinstance(varType, tuple):  # Simple types
            if varType == 'Int':
                self.V[varName] = z3.Int(varName)
            elif varType == 'Bool':
                self.V[varName] = z3.Bool(varName)
            elif varType == 'Real':
                self.V[varName] = z3.Real(varName)
            elif varType == 'String':
                self.V[varName] = z3.String(varName)

            # TODO: there are two variants !!!
            # elif varType == 'BitVec':
            #    self.V[varName] == z3.BitVec()

        else:  # Composed type
            assert len(varType) > 1, f"Specification is incorrect for varName {varName} and varType {varType}"
            varType = varSpec[0]
            if varType == 'IntVector':
                size = varSpec[1]
                self.V[varName] = z3.IntVector(varName, size)
            elif varType == 'BoolVector':
                size = varSpec[1]
                self.V[varName] = z3.BoolVector(varName, size)
            elif varType == 'IntVector':
                size = varSpec[1]
                self.V[varName] = z3.RealVector(varName, size)
            elif varType == 'Array':
                indexSort = self.__fromStrSortToZ3Sort(varSpec[1])
                valuesSort = self.__fromStrSortToZ3Sort(varSpec[2])
                self.V[varName] = z3.Array(varName, indexSort, valuesSort)
            elif varType == 'Function':
                pass  # TODO fix later

    # Parse a variables dictionary and stores them in this class
    def __createVariables(self, graphVariables):
        for varName, varSpec in graphVariables.items():
            if isinstance(varSpec, tuple):
                varType = varSpec[0]
                if varType == 'Context': # This is special because:   (name , ('Context', Value, Sort)). Base type is (name, Sort)
                    constVal = varSpec[1]
                    self.V_constants[varName] = constVal
                    varSpec = list(varSpec)[2:]
                    if len(varSpec) == 1:
                        varSpec = varSpec[0]
                    else:
                        varSpec = tuple(varSpec[0])

            self.__createSingleVariableBySpec(varName, varSpec)

            assert varName in self.V, f"Couldn't fix this variable name {varName} !!"


    # Given a sort as a string convert to a real Z3 object sort
    def __fromStrSortToZ3Sort(self, strSort : str):
        if strSort == 'Int':
            return z3.IntSort()
        elif strSort == 'Bool':
            return z3.BoolSort()
        elif strSort == 'String':
            return z3.StringSort()
        elif strSort == 'Real':
            return z3.RealSort()
        elif strSort == 'Array':
            return z3.ArraySort()
        elif strSort == 'BitVec':
            return z3.BitVecSort()
        else:
            assert f"Can't solve the given {strSort} type !"
            return None
        return None

    # Parse a graph dictionary
    def __createTestGraph_fromDict(self,dictSpec: Dict[str, any], graphName):
        graph = nx.DiGraph()
        graph.clear()

        # Step 1: Create all the node firsts and cache the inverse dictionary in the graph from node_id to node instance
        graph.graph['graphName'] = graphName

        nodeIdToInstance: Dict[str, BranchNode] = {}

        # Factory of nodes...too simple to put it now in a different class
        for nodeId, nodeSpec in dictSpec.items():
            assert isinstance(nodeSpec, tuple) and len(nodeSpec) > 0, f"invalid specification for node {nodeId}"
            nodeCond = nodeSpec[0]

            if nodeCond is None:
                nodeInst = FlowNode(id=nodeId)
            else:
                nodeInst = BranchNode(id=nodeId, condition=nodeCond)

            nodeIdToInstance[nodeId] = nodeInst

            # See here all the graphiviz attributes: https://graphviz.org/doc/info/attrs.html
            node_shape = None
            if nodeInst.id == self.entryTestNodeId:
                node_shape = 'doubleoctagon'
            elif nodeInst.nodeType == NodeTypes.BRANCH_NODE:
                node_shape = 'diamond'
            else:
                node_shape = 'box'

            #'square' if nodeInst.nodeType == NodeTypes.BranchNode else 'circle'
            nodeGraphParentName = nodeInst.getGraphNameFromNodeId()
            assert nodeGraphParentName in self.graphColors, f"Looking for graph named {nodeGraphParentName} but it doesn't exist "
            node_color =  self.graphColors[nodeGraphParentName]
            node_fill_color = 'blue' if nodeInst.id == self.entryTestNodeId else 'white'
            node_style = 'filled'
            graph.add_node(nodeInst, shape=node_shape, color=node_color, fillcolor = node_fill_color, style=node_style)

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

                    graph.add_edge(parentNodeInst, succNodeInst)
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
            nodeIdsToInstances = self.mainGraph.graph['nodeIdToInstance']

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
            _findpath(graph=self.mainGraph, currNode=snode,
                      currPath=[], visitedNodes=set(), outAllPaths=allpaths)

        return allpaths

    # A function to fix the node finding inside a graph
    def __fixNodeInstance(self, node):
        if isinstance(node, str):
            nodeIdToInstance = self.mainGraph.graph['nodeIdToInstance']
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
        for node in self.mainGraph.nodes:
            print(node)

        print("Graph edges: ")
        for edge in self.mainGraph.edges:
            start = edge[0]
            end = edge[1]
            print(f"start from {start.id} end {end.id}")

        print("In Degrees: ", self.mainGraph.in_degree([node for node in self.mainGraph.nodes]))
        print("Out Degrees: ", self.mainGraph.out_degree([node for node in self.mainGraph.nodes]))

    def __getPathConditions(self, path):
        assert isinstance(path, list) and len(path) > 0 and isinstance(path[0], BranchNode)
        pathLen = len(path)
        outCOnditions = []
        for nodeIndex in range(pathLen):


            currNode = path[nodeIndex]
            if currNode.nodeType != NodeTypes.BRANCH_NODE:
                continue

            nextNode = path[nodeIndex + 1] if (nodeIndex + 1 < pathLen) and len(currNode.valuesAndNext) > 0 else None

            # Fix the condition to solve
            condToSolve = currNode.expression
            if nextNode != None:
                # Is inverse branch for next node ?
                if 'False' in currNode.valuesAndNext and currNode.valuesAndNext['False'] == nextNode.id:
                    condToSolve = 'Not(' + condToSolve + ')'
                else:
                    assert currNode.valuesAndNext['True'] == nextNode.id

            outCOnditions.append(condToSolve)

        return outCOnditions

    # Debugging the graph...
    def debugGraph(self, outputGraphFile=None):
        print("Drawing and showing the graph")
        #nx.draw_networkx(self.graph)
        #plt.pyplot.show()
        A = to_agraph(self.mainGraph)
        A.layout('dot')
        A.draw(outputGraphFile)

        # Let's inspect the graph...
        self.__debugInspectGraph()

        print("Checking all paths inside the graph !")
        allpaths = self.__getAllPaths()
        self.__debugPrintPaths(allpaths)

        print("\n\nGetting all used variables inside branches ")
        print(self.V)  # print(getAllVariables(graph))

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solveOfflineStaticGraph(self, outputCsvFile=None, debugLogging=False):
        V = self.V

        fieldNamesList = [key for key in self.V_constants] # Put the constants firsts
        fieldNamesList.extend([key for key in self.V if key not in self.V_constants])
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
            if debugLogging:
                print(f"Analyzing path {index}: [{self.__debugPrintSinglePath(P)}]")
                print("-------------------------")
            conditions_str = self.__getPathConditions(allpaths[index])

            conditions_z3 = []
            for s in conditions_str:
                cond = eval(s)
                conditions_z3.append(cond)

            solver = Solver()
            # Add all the required conditions for the constant variables
            for constName, constValue in self.V_constants.items():
                solver.add(self.V[constName] == constValue)

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

                    if csv_stream:
                        csv_stream.writerow(rowContent)
            else:
                if debugLogging:
                    print("No solution exists for this path")

