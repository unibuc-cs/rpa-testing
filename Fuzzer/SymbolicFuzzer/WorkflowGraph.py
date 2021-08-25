import copy

import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph
from enum import Enum
from Executor_NodesExec import *
import json
import  csv
from WorkflowGraphBaseNode import *


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
        print("== Symbolic variables: \n", self.dataStoreTemplate.SymbolicValues.keys())  # print(getAllVariables(graph))
        print("== All variables: \n", self.dataStoreTemplate.Values.keys())  # print(getAllVariables(graph))

    # TODO: the two functions below need to be refactored !!
    def __getPathConditions(self, path, executionContext : SMTPath):
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
                        condToSolve = self.astFuzzerNodeExecutor.getInverseOfSymbolicExpresion(condToSolve)#'Not(' + condToSolve + ')'
                    else:
                        assert currNode.valuesAndNext['True'] == nextNode.id

                    outCOnditions.append(condToSolve)
            else:
                if currNode.expression:
                    self.astFuzzerNodeExecutor.executeNode(currNode.expression, executionContext)

        return outCOnditions

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solveOfflineStaticGraph(self, outputCsvFile=None, debugLogging=False, astFuzzerNodeExecutor=None):
        fieldNamesList = [key for key in self.dataStoreTemplate.Values.keys()]
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
            # Reset the datastore variables to default variables before each running case
            newPath = SMTPath(conditions_z3=[],
                              dataStore=copy.deepcopy(self.dataStoreTemplate),
                              start_node=None)

            pathStr = None
            if debugLogging:
                pathStr = self.__debugPrintSinglePath(P)
                print(f"Analyzing path {index}: [{pathStr}]")
                print("-------------------------")
            conditions_str = self.__getPathConditions(path = allpaths[index], executionContext=newPath)

            conditions_z3 = []
            for conditionInStr in conditions_str:
                #print(f"Current condition {s} ...")
                conditionInZ3 = self.astFuzzerNodeExecutor.convertStringExpressionTOZ3(conditionInStr, newPath.dataStore)
                conditions_z3.append(conditionInZ3)

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
                # Hold a temporary list of arrays being filled
                # Note that we need those to be constructed one by one indices...as indices are interpreted as individual parameters inside SMT solver
                arraysFilledBySMT : Dict[str, Dict[int, any]]  = {} # arrayName ->  {index -> value}

                if csv_stream != None:
                    rowContent = {}
                    # For each variabile in the model, output its storage
                    for decl in m.decls():
                        # Get the value of declaration from the model
                        # --------------------------------
                        valueOfDecl = m[decl]
                        if z3.is_int_value(valueOfDecl):
                            valueOfDecl = valueOfDecl.as_long()
                        elif z3.is_real(valueOfDecl):
                            valueOfDecl = float(valueOfDecl.as_decimal(prec=2))

                        elif z3.is_bool(valueOfDecl):
                            valueOfDecl = True if z3.is_true(valueOfDecl) else False

                        # If needed, fill in the variable inside our output variables list
                        #----------------------------------
                        declAsString = str(decl)
                        isModelVariableNeededForOutput = declAsString in set_fieldNamesList
                        isArrayBeingFilled = False
                        if isModelVariableNeededForOutput is False:
                            # Check the array indices too
                            if "__" in declAsString:
                                splitByIndexAddressing = declAsString.split("__")
                                try:
                                    index = int(splitByIndexAddressing[-1])
                                    arrayName = "".join(splitByIndexAddressing[:-1])
                                    if arrayName in set_fieldNamesList:
                                        isArrayBeingFilled = True
                                        if arrayName not in arraysFilledBySMT:
                                            arraysFilledBySMT[arrayName] = {}
                                        arraysFilledBySMT[arrayName][index] = valueOfDecl
                                except e:
                                    pass

                        if  isModelVariableNeededForOutput and (isArrayBeingFilled is False):
                            rowContent[declAsString] = valueOfDecl # Output the variable value directly

                    # In the end, add the arrays to the content
                    for arrayFilled_key, arrayFilled_value in arraysFilledBySMT.items():
                        assert arrayFilled_key in set_fieldNamesList, "Did I filled an unnedeed array ??"
                        assert len(arrayFilled_key) > 0 ," Array registered for filling but emtpy ??"
                        strOutForArray = ""
                        for arrIndex, arrValue in arrayFilled_value.items():
                            strOutForArray += f"[{arrIndex}]={arrValue} ; "
                        rowContent[arrayFilled_key] = strOutForArray

                    # Fill in the path for this node
                    if pathStr != None:
                        rowContent["GraphPath"] =pathStr

                    if csv_stream:
                        csv_stream.writerow(rowContent)
            else:
                if debugLogging:
                    print("No solution exists for this path")

    def _executeFlowNode(self, executor: ASTFuzzerNodeExecutor, nodeInst: SymGraphNodeFlow, executionContext : SMTPath):
        assert isinstance(nodeInst, SymGraphNodeFlow)
        if nodeInst.expression:
            executor.executeNode(nodeInst.expression, executionContext=executionContext)

    # Given an smt path in progress (or at begining) this will execute it until finish using DFS and different strategies
    # Will also put new states on the priority queue
    def continuePathExecution(self, currPath : SMTPath, worklist : SMTWorklist):
        assert currPath != None
        currPath.initExecutionContext()

        while not currPath.isFinished():
            # Is this a flow node ? Execute it to persist its sate
            currNode = currPath.getNode()
            if currNode.nodeType != NodeTypes.BRANCH_NODE:  #
                self._executeFlowNode(executor=self.astFuzzerNodeExecutor, nodeInst=currNode, executionContext=currPath)
                currPath.advance()

            # Branch node.. hard decisions :)
            elif currNode.nodeType == NodeTypes.BRANCH_NODE:
                # First, Skip if the node doesn't contain any symbolic variable that links to the user input
                # This is a SOFT requirement, could be changed, left it here for optimization purposes
                if currNode.expression.isAnySymbolicVar(currPath.dataStore) == False:
                    # Just execute the node and exit !
                    # We get a fixed result. Move currNode towards it
                    result = self.astFuzzerNodeExecutor.executeNode(currNode.expression, executionContext=currPath)
                    assert result is not None
                    currPath.advance(str(result))
                else:
                    assert isinstance(currNode, SymGraphNodeBranch)
                    # Check each result branch
                    # Those feasible will be added to the queue, the current execution path will follow on a single of them
                    assert ('False' in currNode.valuesAndNextInst and 'True' in currNode.valuesAndNextInst), "We are expecting both branches to be there currently"

                    # Get both the True and False branches
                    symbolicExpressionForNode_true = self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(currNode.expression, executionContext=currPath)
                    symbolicExpressionForNode_false = self.astFuzzerNodeExecutor.getInverseOfSymbolicExpresion(symbolicExpressionForNode_true)

                    symbolicExpressionForNode_true_inZ3 = self.astFuzzerNodeExecutor.convertStringExpressionTOZ3(symbolicExpressionForNode_true,
                                                                                                                 contextDataStore=currPath.dataStore)
                    symbolicExpressionForNode_false_inZ3 = self.astFuzzerNodeExecutor.convertStringExpressionTOZ3(symbolicExpressionForNode_false,
                                                                                                                  contextDataStore=currPath.dataStore)

                    # Now check which of them are solvable
                    isTrueSolvable = currPath.isNewConditionSolvable(symbolicExpressionForNode_true_inZ3)
                    isTrueSolvable = isTrueSolvable != None and isTrueSolvable != z3.unsat
                    isFalseSolvable = currPath.isNewConditionSolvable(symbolicExpressionForNode_false_inZ3)
                    isFalseSolvable = isFalseSolvable != None and isFalseSolvable != z3.unsat


                    # TODO Ciprian: expose the strategies used in this code for continuation and prioritization
                    if isTrueSolvable and isFalseSolvable:
                        # Both are solvable ! Decide which to follow, which to add to the queue for later
                        # For the one in the queue, decide its priority also
                        pass
                    else:
                        if isTrueSolvable:
                            # Only the true branch is solvable
                            pass
                        elif isFalseSolvable:
                            # Only the false branch is solvable
                            pass
                        else:
                            # No branch is solvable
                            pass

                    # DEBUG HELPER CODE
                    """
                    if "5" in symbolicExpressionForNode:
                        a = 3
                        a +=1
                        symbolicExpressionForNode = self.astFuzzerNodeExecutor.getSymbolicExpressionFromNode(currNode.expression)
                    """


    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solveSymbolically(self, outputCsvFile=None, debugLogging=False, astFuzzerNodeExecutor=None):
        # Setup the output files stuff
        fieldNamesList = [key for key in self.dataStoreTemplate.Values.keys()]
        if debugLogging:
            fieldNamesList.append("GraphPath")
        set_fieldNamesList = set(fieldNamesList)

        csv_stream = None
        if outputCsvFile != None:
            csv_file = open(outputCsvFile, mode='w')
            csv_stream = csv.DictWriter(csv_file, delimiter=',', quotechar='"', quoting=csv.QUOTE_MINIMAL, fieldnames=fieldNamesList)
            csv_stream.writeheader()

        nodeIdsToInstances = self.graphInst.graph['nodeIdToInstance']

        # Get the start nodes list
        start_nodes = [nodeIdsToInstances[self.entryTestNodeId]]

        # Add all starting nodes with equal priority
        statesQueue = SMTWorklist()
        for start_node in start_nodes:
            assert isinstance(start_node, SymGraphNodeFlow), "We were expecting first node to be a flow node, but if " \
                                                             "you really need it as a branch node, just put its condition " \
                                                             "in the starting list below.."
            newPathForNode = SMTPath(conditions_z3=[],
                                     dataStore=copy.deepcopy(self.dataStoreTemplate),
                                     start_node = start_node)
            newPathForNode.priority = 0
            statesQueue.addPath(newPathForNode)

        # Do a DFS with queue from here
        while len(statesQueue) > 0:
            # Extract the top node
            currPath = statesQueue.extractPath()

            # Execute the path continuation in a new context setup (possibly new process)
            self.continuePathExecution(currPath, statesQueue)


