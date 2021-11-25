from abc import ABC, abstractmethod
from enum import Enum

import numpy as np

from SymbolicHelpers import *
from WorkflowGraphBaseNode import *

PRIORITY_COLUMN_NAME = 'priority'

class SymbolicSolversStrategiesTypes(Enum):
    STRATEGY_NONE = 0
    STRATEGY_OFFLINE_ALL = 1,
    STRATEGY_SYMBOLIC_DFS = 2,
    STRATEGY_CONCOLIC = 3
    STRATEGY_EFSM = 4

    @staticmethod
    def from_str(strategyName : str):
        if strategyName  == "STRATEGY_DFS":
            return SymbolicSolversStrategiesTypes.STRATEGY_SYMBOLIC_DFS
        elif strategyName == "STRATEGY_OFFLINE_ALL":
            return SymbolicSolversStrategiesTypes.STRATEGY_OFFLINE_ALL
        elif strategyName == "STRATEGY_CONCOLIC":
            return SymbolicSolversStrategiesTypes.STRATEGY_CONCOLIC
        elif strategyName == "STRATEGY_EFSM":
            return SymbolicSolversStrategiesTypes.STRATEGY_EFSM
        else:
            raise NotImplementedError()
        return None

class BaseSymbolicSolverStrategy(ABC):

    # The workfllow this solver is operating on
    def __init__(self, typeid: SymbolicSolversStrategiesTypes, workflowGraph):
        self.workflowGraph = workflowGraph
        self.typeid = typeid
        self.debuggingOptions : DebuggingOptions = None
        self.args = None

        self.nodeIdsToInstances = self.workflowGraph.graphInst.graph['nodeIdToInstance']
        self.dataStoreTemplate = self.workflowGraph.dataStoreTemplate

        # Output support
        self.output_fieldNamesList = None
        self.output_set_fieldNamesList = None


        self.current_csv_streamHandle = None # Current csv stream where tests are outputed
        self.current_csv_streamIndex = -1 # Current csv index stream where tests are outputed
        self.current_csv_numItemsWritten = sys.maxsize # The number of tests written to the current stream

        super().__init__()

    def getNewInputStream(self):
        self.current_csv_streamIndex += 1
        self.current_csv_numItemsWritten = 0 # The number of tests written to the current stream

        newStreamName = f"{self.args.outputTests_PrefixFile}_{self.current_csv_streamIndex}.csv"
        newCsvFileStream = open(newStreamName, mode='w', newline='')

        self.current_csv_streamHandle = csv.DictWriter(newCsvFileStream, delimiter=',', quotechar='"',
                                                           quoting=csv.QUOTE_MINIMAL,
                                                        fieldnames=self.output_fieldNamesList)
        self.current_csv_streamHandle.writeheader()

    # Initializes some parameters for generated tests output streams
    # With this support and two below functions, the strategy will output the varibles values found and their corresponding solutions
    def init_outputStreamsParams(self):
        self.output_fieldNamesList = []

        if self.debuggingOptions.debug_tests_fullVariablesContent is True:
            self.output_fieldNamesList = [key for key in self.dataStoreTemplate.Values.keys()]
        else:
            for varName, varAnnotation in self.dataStoreTemplate.Annotations.items():
                assert isinstance(varAnnotation, VarAnnotation)
                if varAnnotation.isFromUserInput:
                    self.output_fieldNamesList.append(varName)

        self.output_fieldNamesList.append("priority")
        if self.debuggingOptions.debug_tests_fullPaths:
            self.output_fieldNamesList.append("GraphPath")
        self.output_set_fieldNamesList = set(self.output_fieldNamesList)

        # TODO: add mandatory field and link to the option here

        self.current_csv_streamHandle = None # Current csv stream where tests are outputed
        self.current_csv_streamIndex = -1 # Current csv index stream where tests are outputed
        self.current_csv_numItemsWritten = sys.maxsize # The number of tests written to the current stream


    def getModelOutput(self, modelResult, pathResult : List[str],
                       dataStoreContext, resultIsTextual : bool,
                       debugFullPaths : bool,
                       debugPathIndex : int):
        # Get one output row for csv extract
        # Hold a temporary list of arrays being filled
        # Note that we need those to be constructed one by one indices...as indices are interpreted as individual parameters inside SMT solver
        arraysFilledBySMT: Dict[str, Dict[int, any]] = {}  # arrayName ->  {index -> value}

        generatedInput = {}

        # Step 1: Use the dataStore to fill out first
        for varName, varValue in dataStoreContext.Values.items():
            isVariableNeededForOutput = varName in self.output_fieldNamesList
            if not isVariableNeededForOutput:
                continue

            isArrayBeingFilled = dataStoreContext.isVariableRepresentedAsList(varName)

            # Simple variable case
            if isArrayBeingFilled is False:
                generatedInput[varName] = varValue  # Output the variable value directly
            else:
                # Array filled by SMT, cache the values there, they will be outputed later
                arrayName = varName
                if arrayName not in arraysFilledBySMT:
                    arraysFilledBySMT[arrayName] = {}

                varInternalContent: List[any] = varValue.getAllContent()

                for varInternalContent_index, varInternalContent_value in enumerate(varInternalContent):
                    arraysFilledBySMT[arrayName][varInternalContent_index] = varInternalContent_value

        # Step 2: Then, if a model is used - for each variabile in the model, output from its storage and override previous values
        if modelResult is not None:
            arraysFilledBySMT: Dict[str, Dict[int, any]] = {}  # arrayName ->  {index -> value}

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
                    generatedInput[declAsString] = valueOfDecl  # Output the variable value directly

        # In the end, add the arrays to the content
        for arrayFilled_key, arrayFilled_value in arraysFilledBySMT.items():
            assert arrayFilled_key in self.output_fieldNamesList, "Did I filled an unnedeed array ??"
            assert len(arrayFilled_key) > 0, " Array registered for filling but emtpy ??"

            # On textual result, display the array as a string with each index used and its value
            if resultIsTextual is True:
                outputArrayResult = ""
                for arrIndex, arrValue in arrayFilled_value.items():
                    outputArrayResult += f"[{arrIndex}]={arrValue} ; "
            else:
                # Non textual output, generate the array as a list - take the boundary from annotation or from the indices used
                assert arrayFilled_key in dataStoreContext.Annotations
                arrayAnnotation = dataStoreContext.Annotations[arrayFilled_key]
                targetArraySize = None
                if arrayAnnotation is not None and arrayAnnotation.bounds is not None:
                    targetArraySize = int(arrayAnnotation.bounds)

                allIndicesUsedByArray = list(arrayFilled_value.keys())
                allIndicesUsedByArray = [int(x) for x in allIndicesUsedByArray]
                maxIndexUsedByArray = 0 if len(allIndicesUsedByArray) == 0 else max(allIndicesUsedByArray)

                targetArraySize = max(maxIndexUsedByArray + 1, targetArraySize)
                outputArrayResult = [sys.maxsize for i in range(targetArraySize)]

                for arrIndex, arrValue in arrayFilled_value.items():
                    outputArrayResult[arrIndex] = arrValue

            generatedInput[arrayFilled_key] = outputArrayResult

        # Fill in the path for this node if requested
        if debugFullPaths != False and debugFullPaths != None:
            generatedInput["GraphPath"] = self.workflowGraph.debugPrintSinglePath(pathResult)

        return generatedInput

    # Outputs the results from a model after the output stream was initialized with the function above
    def streamOutModel(self, modelResult, priorityUsedForPath : int, pathResult : List[str],
                       debugPathIndex = None, dataStoreContext=None):
        # Print debug all declarations
        # Use the model declarations if exists
        if modelResult is not None:
            for d in modelResult.decls():
                if self.debuggingOptions.debug_consoleOutput:
                    print(f"{d.name()}={modelResult[d]}")
        # Use the datastore values (used for example in the concolic case)
        else:
            assert dataStoreContext is not None, "Both model and data store are none ?? What are you trying to stream out ?!"

            if self.debuggingOptions.debug_consoleOutput:
                dataStoreContext.printDebugValues()

        rowContent = self.getModelOutput(modelResult=modelResult, pathResult=pathResult,
                            dataStoreContext=dataStoreContext, resultIsTextual=True,
                            debugFullPaths=self.debuggingOptions.debug_tests_fullPaths,
                            debugPathIndex=debugPathIndex)
        rowContent[PRIORITY_COLUMN_NAME] = priorityUsedForPath

        if self.debuggingOptions.debug_consoleOutput:
            pathStr = self.workflowGraph.debugPrintSinglePath(pathResult)
            print(f"Generated path {debugPathIndex}: [{pathStr}]")
            print("-------------------------")

        # Do we need to get a new stream handle ?
        if self.current_csv_numItemsWritten >= self.args.outputTests_MaxTestPerFile:
            self.getNewInputStream() # Now we have a new current stream. Go go go !

        assert self.current_csv_streamHandle is not None
        self.current_csv_streamHandle.writerow(rowContent)
        self.current_csv_numItemsWritten += 1

    # Solve the given graph
    @abstractmethod
    def solve(self, outputCsvFile=None, debugLogging=False, otherArgs=None):
        pass

class AllStatesOnesSolver(BaseSymbolicSolverStrategy):

    def __init__(self, workflowGraph):
        super().__init__(SymbolicSolversStrategiesTypes.STRATEGY_OFFLINE_ALL, workflowGraph)

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solve(self, args):
        self.args = args
        self.outputTests_PrefixFile = args.outputTests_PrefixFile
        self.debuggingOptions = args.debuggingOptions

        # Setup the output files stuff
        self.init_outputStreamsParams()

        #condA = 'V["loan"] < 1000' # Just a dummy test to evaluate a simple condition...
        #eval(condA)
        allpaths = self.workflowGraph.getAllPaths()

        for index, P in enumerate(allpaths):
            # Reset the datastore variables to default variables before each running case
            newPath = SMTPath(parentWorkflowGraph=self,
                              initial_conditions_smt=self.dataStoreTemplate.getVariablesSMTConditions(),
                              dataStore=copy.deepcopy(self.dataStoreTemplate),
                              start_nodeId=self.workflowGraph.entryTestNodeId,
                              debugFullPathEnabled=self.debuggingOptions.debug_tests_fullPaths,
                              debugNodesHistoryExplored=self.debuggingOptions.debug_tests_fullPaths)

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
                if self.debuggingOptions.debug_consoleOutput:
                    print("Found a solution")
                modelResult = solver.model()
                self.streamOutModel(modelResult=modelResult,
                                    priorityUsedForPath=InputSeed.DEFAULT_PRIORITY,
                                    pathResult=P,
                                    debugPathIndex=index,
                                    dataStoreContext=newPath.dataStore)

            else:
                if self.debuggingOptions.debug_consoleOutput:
                    print("No solution exists for this path")

class DFSSymbolicSolverStrategy(BaseSymbolicSolverStrategy):

    def __init__(self, workflowGraph):
        super().__init__(SymbolicSolversStrategiesTypes.STRATEGY_SYMBOLIC_DFS, workflowGraph)

    # Given an smt path in progress (or at begining) this will execute it until finish using DFS and different strategies
    # Will also put new states on the priority queue
    def continuePathExecution(self, currPath : SMTPath, worklist : SMTWorklist, concolicStrategy=False): # SMTPath
        assert currPath != None
        currPath.initExecutionContext()

        while not currPath.isFinished():
            # Is this a flow node ? Execute it to persist its sate
            currNode = currPath.getNode()

            if currNode.nodeType != NodeTypes.BRANCH_NODE:  #
                self.workflowGraph._executeAsFlowNode(nodeInst=currNode, executionContext=currPath)
                currPath.advance()
            # Branch node.. hard decisions :)
            elif currNode.nodeType == NodeTypes.BRANCH_NODE:
                # First, Skip if the node doesn't contain any symbolic variable that links to the user input
                # This is a SOFT requirement, could be changed, left it here for optimization purposes
                if currNode.expression.isAnySymbolicVar(currPath.dataStore) == False:
                    # Just execute the node and exit !
                    # We get a fixed result. Move currNode towards it
                    result = self.workflowGraph._executeAsFlowNode(nodeInst=currNode, executionContext=currPath)
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

                    # In a concolic strategy, just gather the conditions encountered on the path but advance always by
                    # using the actual value of variables in the datastore
                    if concolicStrategy is True:
                        # Take the concrete value of the branch using the current input
                        evalResult = self.workflowGraph._executeAsFlowNode(nodeInst=currNode, executionContext=currPath)
                        assert evalResult is not None and (isinstance(evalResult, bool) or isinstance(evalResult, np.bool_))

                        # Add the expression to the current path (true means that the branch will be taken if condition is valid)
                        takenZ3Condition = None
                        alternativeZ3Condition = None
                        if evalResult is True:
                            takenZ3Condition = symbolicExpressionForNode_true_inZ3
                            alternativeZ3Condition = symbolicExpressionForNode_false_inZ3
                        else:
                            takenZ3Condition = symbolicExpressionForNode_false_inZ3
                            alternativeZ3Condition = symbolicExpressionForNode_true_inZ3

                        currPath.addNewBranchLevel(newConditionInZ3=takenZ3Condition,
                                                   executeNewConditionToo=False,
                                                   concolicEval=evalResult,
                                                   concolicAlternativeBranchZ3Condition=alternativeZ3Condition)

                        currPath.advance(str(evalResult))


                    # In a symbolic strategy, we split the path at this point in to SMT paths, live.
                    else:
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
                            newPath.setStartingNodeId(nextNodeOnFalseBranch.id, isQueuedPathNode=True)
                            newPath.priority = self.scoreNewSymbolicPath(currPath, newPath)
                            worklist.addPath(newPath)
                        else:
                            if isTrueSolvable or isFalseSolvable:
                                if isTrueSolvable:
                                    # Only the true branch is solvable
                                    # DECISION MAKING EXTENSION: there is alwasy the option to put this in the worklist and take another one from the worklist (BFS , IDFS ?)
                                    currPath.addNewBranchLevel(symbolicExpressionForNode_true_inZ3,
                                                               executeNewConditionToo=True)
                                    currPath.setStartingNodeId(nextNodeOnTrueBranch.id, isQueuedPathNode=False)

                                    # DECISION MAKING EXTENSION:  this is needed only on a DFS pure strategy !
                                    currPath.advance('True')

                                elif isFalseSolvable:
                                    # Only the false branch is solvable
                                    # DECISION MAKING EXTENSION: there is alwasy the option to put this in the worklist and take another one from the worklist (BFS , IDFS ?)
                                    currPath.addNewBranchLevel(symbolicExpressionForNode_false_inZ3,
                                                               executeNewConditionToo=True)

                                    currPath.setStartingNodeId(nextNodeOnFalseBranch.id, isQueuedPathNode=False)

                                    # DECISION MAKING EXTENSION:  this is needed only on a DFS pure strategy !
                                    currPath.advance('False')
                            else:
                                # No branch is solvable
                                currPath.forceFinish(withFail=True)

        # If we end here and the path was not forced to fail along run, consider it succesfull
        if currPath.finishStatus != SMTPathState.PATH_FINISHED_FAIL:
            currPath.finishStatus = SMTPathState.PATH_FINISHED_SUCCED

        if currPath.finishStatus == SMTPathState.PATH_FINISHED_SUCCED:
            modelResult = currPath.getSolvedModel() if concolicStrategy is False else None
            self.streamOutModel(modelResult=modelResult,
                                priorityUsedForPath=currPath.priority,
                                pathResult=currPath.debugNodesExplored,
                                debugPathIndex=currPath.debugNumPathsSolvableFound,
                                dataStoreContext=currPath.dataStore)
            currPath.debugNumPathsSolvableFound += 1


    # This is the scoring function that should be overridden in the symbolic case case.
    # You have access to the path previously executed, and the new one.
    # Feel free to add more context, but please be sure that you can't reconstruct things from pathExecuted and these
    # parameters already !
    def scoreNewSymbolicPath(self, prevPath : SMTPath,
                             newPath : SMTPath):
        # Basic impl, that takes as priority the level in the tree where the branching occurred
        priority = prevPath.levelInBranchTree
        return priority

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solve(self,args):
        # Setup the output files stuff
        self.args = args
        self.outputTests_PrefixFile = args.outputTests_PrefixFile
        self.debuggingOptions = args.debuggingOptions

        # Setup the output files stuff
        self.init_outputStreamsParams()

        # Get the start nodes list
        start_nodes = [self.workflowGraph.entryTestNodeId]

        # Add all starting nodes with equal priority
        statesQueue = SMTWorklist()
        for start_nodeId in start_nodes:
            """
            assert isinstance(self.workflowGraph.getNodeInstanceById(start_nodeId), SymGraphNodeFlow), "We were expecting first node to be a flow node, but if " \
                                                             "you really need it as a branch node, just put its condition " \
                                                             "in the starting list below.."
            """

            newPathForNode = SMTPath(parentWorkflowGraph=self.workflowGraph,
                                     initial_conditions_smt=self.dataStoreTemplate.getVariablesSMTConditions(),
                                     dataStore=copy.deepcopy(self.dataStoreTemplate),
                                     start_nodeId=start_nodeId,
                                     debugFullPathEnabled=self.debuggingOptions.debug_tests_fullPaths,
                                     debugNodesHistoryExplored=[])
            newPathForNode.priority = InputSeed.DEFAULT_PRIORITY # This is the start priority.....highest
            statesQueue.addPath(newPathForNode)

        # Do a DFS with queue from here
        while len(statesQueue) > 0:
            # Extract the top node
            currPath = statesQueue.extractPath()

            # Execute the path continuation in a new context setup (possibly new process)
            self.continuePathExecution(currPath, statesQueue)
