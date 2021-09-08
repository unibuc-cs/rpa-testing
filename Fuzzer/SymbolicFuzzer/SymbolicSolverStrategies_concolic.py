import random

from SymbolicSolverStrategies import *
import pandas as pd
from typing import Dict, List
from Parser_DataTypes import ConcolicInputSeed
import numpy as np
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
    # returns a list of inputs considered as seeds
    def getInputSeeds(self, inputSeedsFile : str, numSeedsToGenerate : int) -> List[ConcolicInputSeed]:
        PRIORITY_COLUMN_NAME = 'priority'

        # Read from the inputs seeds file
        userInputVariables : List[str] = self.dataStoreTemplate.getUserInputVariables()

        inputSeedsDf = pd.read_csv(inputSeedsFile).fillna('')
        list_of_column_names = list(inputSeedsDf.columns)
        assert PRIORITY_COLUMN_NAME in list_of_column_names, "priority column is missing from your seeds csv file !!"
        list_of_column_names.remove(PRIORITY_COLUMN_NAME)

        # Check if they are the same content
        if len(list_of_column_names) != len(userInputVariables) or  \
            sorted(list_of_column_names)  != sorted(userInputVariables):
                assert False, "not all input variables are defined by the inputs seeds file. Or too many ! THey must match "''

        outRes : List[Dict[str,str]] = []
        prioritiesUsedInSeedFile = [ConcolicInputSeed.DEFAULT_PRIORITY] # The list of priorities to be used later
        for index, row in inputSeedsDf.iterrows():
            inputSeedContent = {}
            for varName in userInputVariables:
                assert varName in row, "sanity check on top of above"
                # Checking for nan values
                if isinstance(row[varName], str) and row[varName].strip() == '':
                    assert False, f"Variable {varName} is nan !!! Please fill in the value"

                if self.dataStoreTemplate.isVariableOfTypeList(varName):
                    inputSeedContent[varName] = ast.literal_eval(row[varName])
                else:
                    inputSeedContent[varName] = row[varName]


            inpSeed : ConcolicInputSeed = ConcolicInputSeed()
            inpSeed.inputSeed = inputSeedContent
            inpSeed.priority = int(row[PRIORITY_COLUMN_NAME])
            prioritiesUsedInSeedFile.append(inpSeed.priority)
            outRes.append(inpSeed)
            outRes.append(inputSeedContent)

        # Generate random the number of requested seeds
        for indexRandomSeed in range(numSeedsToGenerate):
            inputSeedContent = {}
            for varName in userInputVariables:
                # Start with the default value, either specified or type default value
                varValue = self.dataStoreTemplate.getDefaultValueForVar(varName)
                assert varValue is not None, "Default value can't be retrived !"

                # Try to get a better value from annotation if they exist
                varRandomValue = self.dataStoreTemplate.getRandomValueForVar(varName)
                if varRandomValue is not None:
                    varValue = varRandomValue

                assert varValue is not None, f"Couldn't create seed value for variable {varName}"
                inputSeedContent[varName] = varRandomValue

            inpSeed : ConcolicInputSeed = ConcolicInputSeed()
            inpSeed.inputSeed = inputSeedContent
            inpSeed.priority = random.choice(prioritiesUsedInSeedFile) # Chose a priority among the one already used !
            outRes.append(inpSeed)

        return outRes

    def addInputSeedsToWorkList(self, allInputSeeds : List[ConcolicInputSeed], worklist : SMTWorklist):
        for inputSeed in allInputSeeds:
            # Create a datastore from template and put the input seed on it
            dataStoreInst = copy.deepcopy(self.dataStoreTemplate)
            dataStoreInst.setInputSeed(inputSeed)

            # Create the initial set of conditions (boundaries, assumtpions initial) and force variables
            # set by by seed value
            initialSMTConditions = self.dataStoreTemplate.getVariablesSMTConditions(forceInputSeed=inputSeed.input),

            # Create the SMT path
            newPathForNode = SMTPath(parentWorkflowGraph=self.workflowGraph,
                                     initial_conditions_smt=initialSMTConditions,
                                     dataStore=dataStoreInst,
                                     start_nodeId=self.workflowGraph.graphInst,
                                     debugFullPathEnabled=self.debugLogging,
                                     debugNodesHistoryExplored=[],
                                     priority=inputSeed.priority)

            # Add to the worklist
            worklist.addPath(newPathForNode)

    # Solve all feasible paths inside the graph and produce optionally a csv output inside a given csv file
    def solve(self, outputCsvFile=None, debugLogging=False, otherArgs=None):
        # Setup the output files stuff
        self.init_outputStream(outputCsvFile, debugLogging)
        self.outputCsvFile = outputCsvFile
        self.debugLogging = debugLogging
        self.otherArgs = otherArgs

        # Get the input seeds
        inputSeeds = self.getInputSeeds(inputSeedsFile=self.otherArgs.seedsFile, numSeedsToGenerate=self.otherArgs.numRandomGeneratedSeeds) # [self.workflowGraph.entryTestNodeId]

        # Transform the inputSeeds to SMTPaths and add them to the working list
        statesQueue = SMTWorklist()
        self.addInputSeedsToWorkList(inputSeeds, statesQueue)


        # Do a DFS with queue from here
        while len(statesQueue) > 0:
            # Extract the top node
            currPath = statesQueue.extractPath()

            # Execute the path continuation in a new context setup (possibly new process)
            self.continuePathExecution(currPath, statesQueue)

        print("Finished concolic !")

