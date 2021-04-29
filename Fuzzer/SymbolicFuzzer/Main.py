# TODO tasks:
# See the interaction graph to extend for dynamic symbolic programming and concolic
# logging support rather than printf

# First install the packages
# pip install pip install z3-solver
# pip install py_expression_eval
# pip install networkx
# pip install pygraphviz

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

# A generic branch node definition
class BranchNode():  # Just an example of a base class
    def __init__(self, id : str, condition : str):
        self.expression = condition
        self.valuesAndNext : Dict[str, str] = {} # A dictionary from expression value to next branch
        self.id = id

    def getVariables(self):
        return None # self.expression.variables() # TODO

    def __str__(self):
        return self.id + " " + str(self.expression)

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

# An interaction point node definition
class InteractionNode(): # TODO, work in progress
    pass


# A symbolic workflow testing assistant starting from a given workflow graph in JSon format and the variables names and their types
# Using Z3 as SMT solver
# Variables
# ============
# ---We currently support the following types of variables:
#       a) Base types:Int, Real, Bool, String, Const (Sort), BitVectors - where sort is one of the others
#       b) When you have a small number of items in a vector:  IntVector, RealVector, BoolVector (each will create in the background the requested number of base types instances)
#       c) When you have large arrays: Array(IndexSort,ValuesSort), where both sorts can be one of the types at a)
#                                       Map(IndexSort, ValuesSort)
#       f) Function mapping: F(...input arity and sorts..., output sort). E.g. f(IntSort(), IntSort(), BoolSort())  f(a,b)->boolean
# There is a parser implemented inside which reads and puts everything in place
# NOTE: use the variables set to put both (graph) model + context variables ! Why ? Maybe context variables are not used
# inside condition branches, but setting them as constants in the model will setup correct output in the given context !
# Technically we can impose arithmetic and logic operations on top of all these variables.
# Strings in particular can impose length boundaries, substrings, to contain given strings, etc - just ask what you need and we'll solve !
# Arrays theory can be enabled with store/select SMT assertions as well which works efficently for large sizes
# One idea is to use aggregates such as _max, _min, _avg as variables then deal with those when producing the output columns.
# !!! this is a TODO task for Ciprian


# Functionalities
# ============
# Init this object by giving the json config with the symbolic graph and variables
# Then you can run the following public functions to get things out of it:
# 0. debugGraph - show the content of the graph visually and in text format for debug purposes
# 1. solveOfflineStaticGraph - no interaction nodes, this will be offline evaluated, the algorithm tries to find all feasible paths
# and output them to a CSV
# 2. solveOfflineDynamicSymbolic - pure symbolic, with interaction nodes that requires feedback from robot
# 3. solveOnlineDynamicSymbolic - concolic, with interaction nodes that requires feedback from robot
# ----------

class SymbolicWorflowTester():
    def __init__(self, name : str, graphDict, graphVariables):
        self.name = name # Name of the model
        self.graph = None # Symbolic graph structure
        self.V = {} # Variables dict
        self.V_constants = {} # Context variables that are given as fixed for the model

        # Create the variables dictionary inside self.V
        self.__createVariables(graphVariables)

        # Create the symbolic graph
        self.graph = self.__createTestGraph_fromDict(graphDict, name)

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
                if varType == 'Const': # This is special because:   (name , ('Const', Value, Sort)). Base type is (name, Sort)
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

        for nodeId, nodeSpec in dictSpec.items():
            assert isinstance(nodeSpec, tuple) and len(nodeSpec) > 0, f"invalid specificiation for node {nodeId}"
            nodeCond = nodeSpec[0]
            nodeInst = BranchNode(id=nodeId, condition=nodeCond)
            nodeIdToInstance[nodeId] = nodeInst
            graph.add_node(nodeInst)

        graph.graph['nodeIdToInstance'] = nodeIdToInstance

        # Step 2: Create the links inside the nodes and graph
        for nodeId, nodeSpec in dictSpec.items():
            nodeSuccessorsSpec = nodeSpec[1]
            assert isinstance(nodeSuccessorsSpec, list), f"Expecting a list here for node successors desc!"

            parentNodeInst = nodeIdToInstance[nodeId]
            for nodeSucc in nodeSuccessorsSpec:
                nextNodeVal = nodeSucc[0]
                nextNodeId = nodeSucc[1]

                succNodeInst = nodeIdToInstance[nextNodeId]
                parentNodeInst.valuesAndNext[nextNodeVal] = nextNodeId

                graph.add_edge(parentNodeInst, succNodeInst)

        return graph

    # A function to collect all paths in the graph. For loops it just consider one iteration case as long as every branch is covered
    # For infinite graphs we'll consider IDA approach
    def __getAllPaths(self):
        # Get all the starting nodes (in degree = 0)
        start_nodes = []
        for node in self.graph.nodes:
            node = self.__fixNodeInstance(node)
            if self.graph.in_degree[node] == 0:
                start_nodes.append(node)

        # print(start_nodes[0].name)

        allpaths = []

        def _findpath(graph, currNode, currPath, outAllPaths):
            currPath.append(currNode)
            if graph.out_degree[currNode] == 0:  # leaf node ?
                outAllPaths.append(currPath)
            else:
                # For each successor add this node to a copy of the list and iterate on that path
                for succNode in graph.successors(currNode):
                    succNode = self.__fixNodeInstance(succNode)
                    newCurrPath = copy.deepcopy(currPath)
                    _findpath(graph, succNode, newCurrPath, outAllPaths)

        # From each starting node, run a directed search path until leafs
        for snode in start_nodes:
            _findpath(self.graph, snode, [], allpaths)

        return allpaths

    # A function to fix the node finding inside a graph
    def __fixNodeInstance(self, node):
        if isinstance(node, str):
            nodeIdToInstance = self.graph.graph['nodeIdToInstance']
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
        for node in self.graph.nodes:
            print(node)

        print("Graph edges: ")
        for edge in self.graph.edges:
            start = edge[0]
            end = edge[1]
            print(f"start from {start.id} end {end.id}")

        print("In Degrees: ", self.graph.in_degree([node for node in self.graph.nodes]))
        print("Out Degrees: ", self.graph.out_degree([node for node in self.graph.nodes]))

    def __getPathConditions(self, path):
        assert isinstance(path, list) and len(path) > 0 and isinstance(path[0], BranchNode)
        pathLen = len(path)
        outCOnditions = []
        for nodeIndex in range(pathLen):
            currNode: BranchNode = path[nodeIndex]
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
        A = to_agraph(self.graph)
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

def demo_bankLoanExample():
    variables = {'loan' : 'Real', 'term' : 'Int', 'context_userId' : ('Const', 2, 'Int')}
    bankLoanGraph = {'node_loanTest0' : ('V["loan"] < 1000', [('True', 'term_test0'), ('False', 'node_loanTest1')]),
                    'node_loanTest1' : ('And(V["loan"] >= 1000, V["loan"] < 10000)', [('True', 'term_test0'), ('False', 'sinkF')]),
                    'term_test0' : ('V["term"] < 5', [('True', 'sinkT'), ('False', 'sinkF')]),
                    'sinkT' :  ('True', []),
                    'sinkF': ('True', [])
                    }

    bankLoanWorkTester = SymbolicWorflowTester(name="bankLoanWorkflow", graphDict=bankLoanGraph, graphVariables=variables)
    bankLoanWorkTester.debugGraph(outputGraphFile="debugGraph.png")
    bankLoanWorkTester.solveOfflineStaticGraph(outputCsvFile="generatedTests.csv", debugLogging=False)

if __name__ == "__main__":
    # Creating the graph now from a given dictionary
    demo_bankLoanExample()

    # TODO and usecases:
    #   -   demo with foreach
    #   -   interaction node usage
    #   -   others

