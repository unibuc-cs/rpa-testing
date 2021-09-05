from SymbolicSolverStrategies import *
import pandas as pd

# Ideas:
"""

Create a new input class ( added to SMTPath ? ), A priority Worklist - reuse the one for symbolic
Every path will be an SMTPath aggregating conditions. At each run we put the datastore context as defined by the input executed
We just execute the input, no realtime branching, BUT record the branch condition and taken branch in SMTPath

"""

class ConcolicSolverStrategy(DFSSymbolicSolverStrategy):

    def __init__(self, workflowGraph):
        super().__init__(workflowGraph)
        self.typeid = SymbolicSolversStrategiesTypes.STRATEGY_CONCOLIC

    # Given an input seeds file and a number of seeds to generate randomly (according to certain specs) additionally,
    # returns a list of inputs considered as seeds, where each entry is a dict from variable name to its value
    def getInputSeeds(self, inputSeedsFile : str, numSeedsToGenerate : int) -> List[Dict[str,str]]:
        # Read from the inputs seeds file
        userInputVariables : List[str] = self.dataStoreTemplate.getUserInputVariables()

        inputSeedsDf = pd.read_csv(inputSeedsFile)
        list_of_column_names = list(inputSeedsDf.columns)

        if len(list_of_column_names) != len(userInputVariables) or  \
            sorted(list_of_column_names)  != sorted(userInputVariables):
                assert False, "not all input variables are defined by the inputs seeds file"''

        outRes : List[Dict[str,str]] = []
        for index, row in inputSeedsDf.iterrows():
            inputSeedNew = {}
            for varName in userInputVariables:
                inputSeedNew['varName'] = row['varName']
            outRes.append(inputSeedNew)

        # Generate random the number of requested seeds
        for indexRandomSeed in range(numSeedsToGenerate):
            inputSeedNew = {}
            for varName in userInputVariables:
                foundValue = False
                if varName in self.dataStoreTemplate.Annotations:
                    varAnnotation : VarAnnotation = self.dataStoreTemplate.Annotations[varName]
                    assert isinstance()
                    inputSeedNew['varName'] = varAnnotation




            outRes.append(inputSeedNew)

        pass

   # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solve(self, outputCsvFile=None, debugLogging=False, otherArgs=None):
        # Setup the output files stuff
        self.init_outputStream(outputCsvFile, debugLogging)
        self.outputCsvFile = outputCsvFile
        self.debugLogging = debugLogging

        # Get the start nodes list
        start_nodes = self.getInputSeeds() # [self.workflowGraph.entryTestNodeId]

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
                                     debugFullPathEnabled=debugLogging,
                                     debugNodesHistoryExplored=[])
            newPathForNode.priority = 0 # TODO Ciprian decisions: start node priority ?
            statesQueue.addPath(newPathForNode)

        # Do a DFS with queue from here
        while len(statesQueue) > 0:
            # Extract the top node
            currPath = statesQueue.extractPath()

            # Execute the path continuation in a new context setup (possibly new process)
            self.continuePathExecution(currPath, statesQueue)

