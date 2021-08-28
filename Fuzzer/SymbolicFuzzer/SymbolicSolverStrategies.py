from abc import ABC, abstractmethod
from enum import Enum
from SymbolicHelpers import *
from WorkflowGraphBaseNode import *

class SymbolicSolversStrategiesTypes(Enum):
    STRATEGY_NONE = 0
    STRATEGY_OFFLINE_ALL = 1,
    STRATEGY_DFS = 2

    @staticmethod
    def from_str(strategyName : str):
        if strategyName  == "STRATEGY_DFS":
            return SymbolicSolversStrategiesTypes.STRATEGY_DFS
        elif strategyName == "STRATEGY_OFFLINE_ALL":
            return SymbolicSolversStrategiesTypes.STRATEGY_OFFLINE_ALL
        else:
            raise NotImplementedError()
        return None

class BaseSymbolicSolverStrategy(ABC):

    # The workfllow this solver is operating on
    def __init__(self, typeid: SymbolicSolversStrategiesTypes, workflowGraph):
        self.workflowGraph = workflowGraph
        self.typeid = typeid

        self.nodeIdsToInstances = self.workflowGraph.graphInst.graph['nodeIdToInstance']
        self.dataStoreTemplate = self.workflowGraph.dataStoreTemplate

        # Output support
        self.output_fieldNamesList = None
        self.output_set_fieldNamesList = None
        self.output_csv_stream = None

        super().__init__()

    # Initializes an output csv file at the given file name and current working dir
    # With this support and two below functions, the strategy will output the varibles values found and their corresponding solutions
    def init_outputStream(self, outputCsvFile, debugLogging):
        self.output_fieldNamesList = [key for key in self.dataStoreTemplate.Values.keys()]
        if debugLogging:
            self.output_fieldNamesList.append("GraphPath")
        self.output_set_fieldNamesList = set(self.output_fieldNamesList)

        self.output_csv_stream = None
        if outputCsvFile != None:
            csv_file = open(outputCsvFile, mode='w')
            self.output_csv_stream = csv.DictWriter(csv_file, delimiter=',', quotechar='"', quoting=csv.QUOTE_MINIMAL,
                                                    fieldnames=self.output_fieldNamesList)
            self.output_csv_stream.writeheader()

    # Outputs the results from a model after the output stream was initialized with the function above
    def streamOutModel(self, modelResult, pathResult : List[any],
                       debugLoggingEnabled, debugPathIndex = None):
        # Print debug all declarations
        for d in modelResult.decls():
            if debugLoggingEnabled:
                print(f"{d.name()}={modelResult[d]}")

        # Get one output row for csv extract
        # Hold a temporary list of arrays being filled
        # Note that we need those to be constructed one by one indices...as indices are interpreted as individual parameters inside SMT solver
        arraysFilledBySMT: Dict[str, Dict[int, any]] = {}  # arrayName ->  {index -> value}

        if self.output_csv_stream != None:
            rowContent = {}
            # For each variabile in the model, output its storage
            for decl in modelResult.decls():
                # Get the value of declaration from the model
                # --------------------------------
                valueOfDecl = modelResult[decl]
                if z3.is_int_value(valueOfDecl):
                    valueOfDecl = valueOfDecl.as_long()
                elif z3.is_real(valueOfDecl):
                    valueOfDecl = float(valueOfDecl.as_decimal(prec=2))

                elif z3.is_bool(valueOfDecl):
                    valueOfDecl = True if z3.is_true(valueOfDecl) else False

                # If needed, fill in the variable inside our output variables list
                # ----------------------------------
                declAsString = str(decl)
                isModelVariableNeededForOutput = declAsString in self.output_fieldNamesList
                isArrayBeingFilled = False
                if isModelVariableNeededForOutput is False:
                    # Check the array indices too
                    if "__" in declAsString:
                        splitByIndexAddressing = declAsString.split("__")
                        try:
                            index = int(splitByIndexAddressing[-1])
                            arrayName = "".join(splitByIndexAddressing[:-1])
                            if arrayName in self.output_set_fieldNamesList:
                                isArrayBeingFilled = True
                                if arrayName not in arraysFilledBySMT:
                                    arraysFilledBySMT[arrayName] = {}
                                arraysFilledBySMT[arrayName][index] = valueOfDecl
                        except e:
                            pass

                if isModelVariableNeededForOutput and (isArrayBeingFilled is False):
                    rowContent[declAsString] = valueOfDecl  # Output the variable value directly

            # In the end, add the arrays to the content
            for arrayFilled_key, arrayFilled_value in arraysFilledBySMT.items():
                assert arrayFilled_key in self.output_fieldNamesList, "Did I filled an unnedeed array ??"
                assert len(arrayFilled_key) > 0, " Array registered for filling but emtpy ??"
                strOutForArray = ""
                for arrIndex, arrValue in arrayFilled_value.items():
                    strOutForArray += f"[{arrIndex}]={arrValue} ; "
                rowContent[arrayFilled_key] = strOutForArray

            # Fill in the path for this node if requested
            pathStr = None
            if debugLoggingEnabled:
                pathStr = self.workflowGraph.debugPrintSinglePath(pathResult)
                print(f"Analyzing path {debugPathIndex}: [{pathStr}]")
                print("-------------------------")

            if pathStr != None:
                rowContent["GraphPath"] = pathStr

            if self.output_csv_stream:
                self.output_csv_stream.writerow(rowContent)



    # Solve the given graph
    @abstractmethod
    def solve(self, outputCsvFile=None, debugLogging=False):
        pass

class AllStatesOnesSolver(BaseSymbolicSolverStrategy):

    def __init__(self, workflowGraph):
        super().__init__(SymbolicSolversStrategiesTypes.STRATEGY_OFFLINE_ALL, workflowGraph)

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solve(self, outputCsvFile=None, debugLogging=False):
        self.init_outputStream(outputCsvFile, debugLogging)

        #condA = 'V["loan"] < 1000' # Just a dummy test to evaluate a simple condition...
        #eval(condA)
        allpaths = self.workflowGraph.getAllPaths()

        for index, P in enumerate(allpaths):
            # Reset the datastore variables to default variables before each running case
            newPath = SMTPath(parentWorkflowGraph=self,
                              conditions_z3=self.dataStoreTemplate.getVariablesSMTConditions(),
                              dataStore=copy.deepcopy(self.dataStoreTemplate),
                              start_nodeId=self.workflowGraph.entryTestNodeId)

            conditions_str = self.workflowGraph.getPathConditions(path = allpaths[index], executionContext=newPath)

            conditions_z3 = []
            for conditionInStr in conditions_str:
                #print(f"Current condition {s} ...")
                conditionInZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(conditionInStr, newPath.dataStore)
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
                modelResult = solver.model()
                self.streamOutModel(modelResult=modelResult,
                                    pathResult=P,
                                    debugLoggingEnabled=debugLogging,
                                    debugPathIndex=index)

            else:
                if debugLogging:
                    print("No solution exists for this path")

class DFSSymbolicSolverStrategy(BaseSymbolicSolverStrategy):

    def __init__(self, workflowGraph):
        super().__init__(SymbolicSolversStrategiesTypes.STRATEGY_DFS, workflowGraph)

    # Given an smt path in progress (or at begining) this will execute it until finish using DFS and different strategies
    # Will also put new states on the priority queue
    def continuePathExecution(self, currPath : SMTPath, worklist : SMTWorklist ): # SMTPath
        assert currPath != None
        currPath.initExecutionContext()

        while not currPath.isFinished():
            # Is this a flow node ? Execute it to persist its sate
            currNode = currPath.getNode()
            if currNode.nodeType != NodeTypes.BRANCH_NODE:  #
                self.workflowGraph._executeFlowNode(nodeInst=currNode, executionContext=currPath)
                currPath.advance()

            # Branch node.. hard decisions :)
            elif currNode.nodeType == NodeTypes.BRANCH_NODE:
                # First, Skip if the node doesn't contain any symbolic variable that links to the user input
                # This is a SOFT requirement, could be changed, left it here for optimization purposes
                if currNode.expression.isAnySymbolicVar(currPath.dataStore) == False:
                    # Just execute the node and exit !
                    # We get a fixed result. Move currNode towards it
                    result = self.workflowGraph._executeFlowNode(nodeInst=currNode, executionContext=currPath)
                    assert result is not None
                    currPath.advance(str(result))

                else:
                    assert isinstance(currNode, SymGraphNodeBranch)
                    # Check each result branch
                    # Those feasible will be added to the queue, the current execution path will follow on a single of them
                    assert ('False' in currNode.valuesAndNextInst and 'True' in currNode.valuesAndNextInst), "We are expecting both branches to be there currently"

                    # Get both the True and False branches
                    symbolicExpressionForNode_true = self.workflowGraph._getSymbolicExpressionFromNode(nodeInst=currNode,
                                                                                         executionContext=currPath)
                    symbolicExpressionForNode_false = SymbolicExecutionHelpers.getInverseOfSymbolicExpresion(
                        symbolicExpressionForNode_true)

                    symbolicExpressionForNode_true_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(
                        symbolicExpressionForNode_true,
                        contextDataStore=currPath.dataStore)
                    symbolicExpressionForNode_false_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(
                        symbolicExpressionForNode_false,
                        contextDataStore=currPath.dataStore)

                    # Now check which of them are solvable
                    isTrueSolvable = currPath.isNewConditionSolvable(symbolicExpressionForNode_true_inZ3)
                    isTrueSolvable = isTrueSolvable != None and isTrueSolvable != z3.unsat
                    isFalseSolvable = currPath.isNewConditionSolvable(symbolicExpressionForNode_false_inZ3)
                    isFalseSolvable = isFalseSolvable != None and isFalseSolvable != z3.unsat

                    # DECISION MAKING EXTENSION: you can expose the strategies used in this code for continuation and prioritization
                    nextNodeOnFalseBranch: BaseSymGraphNode = currPath.getNextNodeOnBranchResult('False')
                    nextNodeOnTrueBranch: BaseSymGraphNode = currPath.getNextNodeOnBranchResult('True')

                    if isTrueSolvable and isFalseSolvable:
                        # Both are solvable ! Decide which to follow, which to add to the queue for later
                        # For the one in the queue, decide its priority also
                        newPath = copy.deepcopy(currPath)

                        # Default: continue on true
                        currPath.addNewBranchLevel(newConditionInZ3=symbolicExpressionForNode_true_inZ3,
                                                   executeNewConditionToo=True)

                        # FALSE branch
                        # Clone and add the false branch condition to the queue

                        newPath.addNewBranchLevel(symbolicExpressionForNode_false_inZ3,
                                                  executeNewConditionToo=False)
                        newPath.setStartingNodeId(nextNodeOnFalseBranch.id)
                        worklist.addPath(newPath)
                    else:
                        if isTrueSolvable or isFalseSolvable:
                            if isTrueSolvable:
                                # Only the true branch is solvable
                                # DECISION MAKING EXTENSION: there is alwasy the option to put this in the worklist and take another one from the worklist (BFS , IDFS ?)
                                currPath.addNewBranchLevel(symbolicExpressionForNode_true_inZ3,
                                                           executeNewConditionToo=True)
                                currPath.setStartingNodeId(nextNodeOnTrueBranch.id)

                                # DECISION MAKING EXTENSION:  this is needed only on a DFS pure strategy !
                                currPath.advance('True')

                            elif isFalseSolvable:
                                # Only the false branch is solvable
                                # DECISION MAKING EXTENSION: there is alwasy the option to put this in the worklist and take another one from the worklist (BFS , IDFS ?)
                                currPath.addNewBranchLevel(symbolicExpressionForNode_false_inZ3,
                                                           executeNewConditionToo=True)

                                currPath.setStartingNodeId(nextNodeOnFalseBranch.id)

                                # DECISION MAKING EXTENSION:  this is needed only on a DFS pure strategy !
                                currPath.advance('False')
                        else:
                            # No branch is solvable
                            currPath.forceFinish()


    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solve(self, outputCsvFile=None, debugLogging=False):
        # Setup the output files stuff
        fieldNamesList = [key for key in self.dataStoreTemplate.Values.keys()]
        if debugLogging:
            fieldNamesList.append("GraphPath")
        self.set_fieldNamesList = set(fieldNamesList)

        csv_stream = None
        if outputCsvFile != None:
            csv_file = open(outputCsvFile, mode='w')
            csv_stream = csv.DictWriter(csv_file, delimiter=',', quotechar='"', quoting=csv.QUOTE_MINIMAL, fieldnames=fieldNamesList)
            csv_stream.writeheader()

        # Get the start nodes list
        start_nodes = [self.workflowGraph.entryTestNodeId]

        # Add all starting nodes with equal priority
        statesQueue = SMTWorklist()
        for start_nodeId in start_nodes:
            assert isinstance(self.workflowGraph.getNodeInstanceById(start_nodeId), SymGraphNodeFlow), "We were expecting first node to be a flow node, but if " \
                                                             "you really need it as a branch node, just put its condition " \
                                                             "in the starting list below.."

            newPathForNode = SMTPath(parentWorkflowGraph=self.workflowGraph,
                                     conditions_z3=self.dataStoreTemplate.getVariablesSMTConditions(),
                                     dataStore=copy.deepcopy(self.dataStoreTemplate),
                                     start_nodeId=start_nodeId)
            newPathForNode.priority = 0 # TODO Ciprian decisions: start node priority ?
            statesQueue.addPath(newPathForNode)

        # Do a DFS with queue from here
        while len(statesQueue) > 0:
            # Extract the top node
            currPath = statesQueue.extractPath()

            # Execute the path continuation in a new context setup (possibly new process)
            self.continuePathExecution(currPath, statesQueue)

