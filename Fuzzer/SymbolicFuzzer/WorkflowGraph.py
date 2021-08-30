import copy

import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph
from enum import Enum
from Executor_NodesExec import *
import json
import  csv
from WorkflowGraphBaseNode import *
import SymbolicSolverStrategies

class WorkflowGraph:
    def __init__(self, dataStoreTemplate, astFuzzerNodeExecutor):
        # Data needed and filled in when parsing the workflows
        self.entryTestNodeId = None
        self.debugColors = None
        self.mainWorkflowName = None
        self.dataStoreTemplate = dataStoreTemplate
        self.astFuzzerNodeExecutor = astFuzzerNodeExecutor

        # This is the connection to the nx digraph instance
        self.graphInst = nx.DiGraph()
        self.graphInst.clear()

    def setMainWorkflowName(self, name : str):
        self.mainWorkflowName = name
        self.graphInst.graph['graphName'] = name

    # A function to collect all paths in the graph. For loops it just consider one iteration case as long as every branch is covered
    # For infinite graphs we'll consider IDA approach
    def getAllPaths(self):
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

    # A function to fix internally all nodes from node ids (str) to node instances
    def fixAllNodesInstances(self):
        allNodesList = self.graphInst.nodes()
        for nodeInst in allNodesList:
            assert isinstance(nodeInst, BaseSymGraphNode)
            if nodeInst.nodeType == NodeTypes.FLOW_NODE:
                assert isinstance(nodeInst, SymGraphNodeFlow)

                if nodeInst.nextNodeId is None:
                    succesors = self.graphInst.successors(nodeInst)
                    #assert len(succesors) <= 1, " More than 1 successor for a flow node ??"
                    for succ in succesors:
                        nodeInst.nextNodeInst = succ
                        nodeInst.nextNodeId = succ.id
                        break
                    continue

                assert isinstance(nodeInst.nextNodeId, str)
                assert nodeInst.nextNodeInst is None, " ALready converted ??"
                nodeInst.nextNodeInst = self.__fixNodeInstance(nodeInst.nextNodeId)
            elif nodeInst.nodeType == NodeTypes.BRANCH_NODE:
                assert isinstance(nodeInst, SymGraphNodeBranch)
                """
                if nodeInst.nextNodeId is None:
                    succesors = self.graphInst.successors(nodeInst)
                    #assert len(succesors) <= 1, " More than 1 successor for a flow node ??"
                    for succ in succesors:
                        nodeInst.nextNodeInst = succ
                        nodeInst.nextNodeId = succ.id
                        break
                    continue
                """
                for nextNode_branchName, nextNode_branchNodeId in nodeInst.valuesAndNext.items():
                    assert isinstance(nextNode_branchNodeId, str)
                    assert nextNode_branchName not in nodeInst.valuesAndNextInst, " ALready converted ??"
                    nodeInst.valuesAndNextInst[nextNode_branchName] = self.__fixNodeInstance(nextNode_branchNodeId)

    # A function to fix the node finding inside a graph
    # returns from node id to node instance
    def __fixNodeInstance(self, node):
        if isinstance(node, str):
            nodeIdToInstance = self.graphInst.graph['nodeIdToInstance']
            node = nodeIdToInstance[node]
        return node

    def debugPrintSinglePath(self, path):
        pathStr = ""
        for node in path:
            node = self.__fixNodeInstance(node)
            pathStr += str(node.id) + " ; "
        return pathStr

    def debugPrintPaths(self, paths):
        for index, P in enumerate(paths):
            print("--- Path ", index, ": ")
            pathStr = self.debugPrintSinglePath(P)
            print(pathStr)

    def debugInspectGraph(self):
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
        self.debugInspectGraph()

        print("Checking all paths inside the graph !")
        allpaths = self.getAllPaths()
        self.debugPrintPaths(allpaths)

        print("\n\nGetting all used variables inside branches ")
        print("== Symbolic variables: \n", self.dataStoreTemplate.SymbolicValues.keys())  # print(getAllVariables(graph))
        print("== All variables: \n", self.dataStoreTemplate.Values.keys())  # print(getAllVariables(graph))

    # TODO: the two functions below need to be refactored !!
    def getPathConditions(self, path, executionContext : SMTPath):
        assert isinstance(path, list) and len(path) > 0 #and isinstance(path[0], SymGraphNodeBranch)
        pathLen = len(path)
        outCOnditions = []
        for nodeIndex in range(pathLen):
            currNode : BaseSymGraphNode = path[nodeIndex]

            # Add the condition for a branching node
            if currNode.nodeType == NodeTypes.BRANCH_NODE:
                # First, Skip if the node doesn't contain any symbolic variable that links to the user input
                # This is a SOFT requirement, could be changed, left it here for optimization purposes
                if currNode.expression.isAnySymbolicVar(contextDataStore=executionContext.dataStore) == False:
                    continue

                nextNode = path[nodeIndex + 1] if (nodeIndex + 1 < pathLen) and len(currNode.valuesAndNext) > 0 else None
                symbolicExpressionForNode = self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(currNode.expression, executionContext)

                # DEBUG HELPER CODE
                """
                if "5" in symbolicExpressionForNode:
                    a = 3
                    a +=1
                    symbolicExpressionForNode = self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(currNode.expression)
                """

                # Fix the condition to solve
                condToSolve = symbolicExpressionForNode
                if nextNode != None and condToSolve != None:
                    # Is inverse branch for next node ?
                    if 'False' in currNode.valuesAndNext and currNode.valuesAndNext['False'] == nextNode.id:
                        condToSolve = SymbolicExecutionHelpers.getInverseOfSymbolicExpresion(condToSolve)#'Not(' + condToSolve + ')'
                    else:
                        assert currNode.valuesAndNext['True'] == nextNode.id

                    outCOnditions.append(condToSolve)
            else:
                if currNode.expression:
                    self.astFuzzerNodeExecutor.executeNode(currNode.expression, executionContext)

        return outCOnditions

    def _executeAsFlowNode(self, nodeInst: SymGraphNodeFlow, executionContext : SMTPath):
        #assert isinstance(nodeInst, SymGraphNodeFlow)
        if nodeInst.expression:
            return self.astFuzzerNodeExecutor.executeNode(nodeInst.expression, executionContext=executionContext)
        return None

    def _getSymbolicExpressionFromNode(self, nodeInst : SymGraphNodeBranch, executionContext : SMTPath):
        assert isinstance(nodeInst, SymGraphNodeBranch)
        if nodeInst.expression:
            return self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(nodeInst.expression, executionContext=executionContext)
        return None

    # Giving a node id in this workflow, return the node instance
    def getNodeInstanceById(self, nodeId):
        return self.graphInst.graph['nodeIdToInstance'][nodeId]

