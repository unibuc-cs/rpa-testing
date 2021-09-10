import random

import z3

from SymbolicSolverStrategies import *
import pandas as pd
from typing import Dict, List
from Parser_DataTypes import InputSeed
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
    def getInputSeeds(self, inputSeedsFile : str, numSeedsToGenerate : int) -> List[InputSeed]:
        PRIORITY_COLUMN_NAME = 'priority'

        # Read from the inputs seeds file
        self.userInputVariables : List[str] = self.dataStoreTemplate.getUserInputVariables()

        inputSeedsDf = pd.read_csv(inputSeedsFile).fillna('')
        list_of_column_names = list(inputSeedsDf.columns)
        assert PRIORITY_COLUMN_NAME in list_of_column_names, "priority column is missing from your seeds csv file !!"
        list_of_column_names.remove(PRIORITY_COLUMN_NAME)

        # Check if they are the same content
        if len(list_of_column_names) != len(self.userInputVariables) or  \
            sorted(list_of_column_names)  != sorted(self.userInputVariables):
                assert False, "not all input variables are defined by the inputs seeds file. Or too many ! THey must match "''

        outRes : List[Dict[str,str]] = []
        prioritiesUsedInSeedFile = [InputSeed.DEFAULT_PRIORITY] # The list of priorities to be used later
        for index, row in inputSeedsDf.iterrows():
            inputSeedContent = {}
            for varName in self.userInputVariables:
                assert varName in row, "sanity check on top of above"
                # Checking for nan values
                if isinstance(row[varName], str) and row[varName].strip() == '':
                    assert False, f"Variable {varName} is nan !!! Please fill in the value"

                if self.dataStoreTemplate.isVariableRepresentedAsList(varName):
                    inputSeedContent[varName] = ast.literal_eval(row[varName])
                else:
                    inputSeedContent[varName] = row[varName]


            inpSeed : InputSeed = InputSeed()
            inpSeed.content = inputSeedContent
            inpSeed.priority = int(row[PRIORITY_COLUMN_NAME])
            prioritiesUsedInSeedFile.append(inpSeed.priority)
            outRes.append(inpSeed)

        # Generate random the number of requested seeds
        for indexRandomSeed in range(numSeedsToGenerate):
            inputSeedContent = {}
            for varName in self.userInputVariables:
                # Start with the default value, either specified or type default value
                varValue = self.dataStoreTemplate.getDefaultValueForVar(varName)
                assert varValue is not None, "Default value can't be retrived !"

                # Try to get a better value from annotation if they exist
                varRandomValue = self.dataStoreTemplate.getRandomValueForVar(varName)
                if varRandomValue is not None:
                    varValue = varRandomValue

                assert varValue is not None, f"Couldn't create seed value for variable {varName}"
                inputSeedContent[varName] = varValue

            inpSeed : InputSeed = InputSeed()
            inpSeed.content = inputSeedContent
            inpSeed.priority = random.choice(prioritiesUsedInSeedFile) # Chose a priority among the one already used !
            outRes.append(inpSeed)

        return outRes

    def addInputSeedsToWorkList(self, allInputSeeds : List[InputSeed], worklist : SMTWorklist):
        for inputSeed in allInputSeeds:
            # Create a datastore from template and put the input seed on it
            dataStoreInst = copy.deepcopy(self.dataStoreTemplate)
            dataStoreInst.setInputSeed(inputSeed)

            # Create the initial set of conditions (boundaries, assumtpions initial) and force variables
            # set by by seed value
            initialSMTConditions = self.dataStoreTemplate.getVariablesSMTConditions(forceInputSeed=inputSeed.content)

            # Create the SMT path
            newPathForNode = SMTPath(parentWorkflowGraph=self.workflowGraph,
                                     initial_conditions_smt=initialSMTConditions,
                                     dataStore=dataStoreInst,
                                     start_nodeId=self.workflowGraph.entryTestNodeId,
                                     debugFullPathEnabled=self.debugLogging,
                                     debugNodesHistoryExplored=[],
                                     priority=inputSeed.priority)

            # Add to the worklist
            worklist.addPath(newPathForNode)

    def generateNewInputs(self, pathExecuted : SMTPath, statesQueue : SMTWorklist) -> List[SMTPath]:
        assert pathExecuted.finishStatus == SMTPathState.PATH_FINISHED_SUCCED, "Path given was not succesffully finish. Do not call this in this case"

        boundaryIndex : int = pathExecuted.concolicBoundaryIndex
        allOriginalConditions : List[any] = pathExecuted.conditions_smt
        numOriginalConditions = len(allOriginalConditions)
        allConcolicTakenDecisions : Dict[int, bool] = pathExecuted.concolicBranchTaken
        allConcolicDecisionIndices = list(allConcolicTakenDecisions.keys())
        numConcolicConditions = len(allConcolicDecisionIndices)

        iter_origCondition = 0
        iter_concolicCondition = boundaryIndex

        newInputsBuilt : List[SMTPath] = []

        while (iter_origCondition < numOriginalConditions) and (iter_concolicCondition < numConcolicConditions):
            # Store the next index of a concolic decision branch
            next_concolicBranchIndexCondition = allConcolicDecisionIndices[iter_concolicCondition]

            # If we are behind, add the next base condition
            if iter_origCondition < next_concolicBranchIndexCondition:
                iter_origCondition += 1

            # This means we are on the same index, and we should do something to reverse it in the new input !
            elif iter_origCondition == next_concolicBranchIndexCondition:
                changedExpr = SymbolicExecutionHelpers.getInverseOfSymbolicExpresion(allOriginalConditions[iter_origCondition])

                # Check if the solver has a solution with all previous conditions enabled but with this condition changed
                # -----------------
                localSolver = z3.Solver()
                for origCond_index, origCond_value in enumerate(allOriginalConditions):
                    # Ignore only this iterated condition, and append instead the changed one
                    if origCond_index != iter_origCondition:
                        localSolver.add(origCond_value)
                    else:
                        localSolver.add(changedExpr)

                # If the model has a solution, then build the new input
                if localSolver.check() != z3.unsat:
                    # TODO: build a new SMTPath here
                    #SMTPath()
                    # and add to newInputsBuilt
                    # score priority for the new input
                    # add it to the worklist
                    pass
            else:
                assert False, "This case shouldn't happen. We always have to check if they are the same indices, put the right assertion in the model, and increase both iterators"

        return newInputsBuilt

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
            currPath : SMTPath = statesQueue.extractPath()

            # Execute the path continuation in a new context setup (possibly new process)
            self.continuePathExecution(currPath, statesQueue, concolicStrategy=True)

            # Now generate the new inputs based on the previous executed path
            if currPath.finishStatus == SMTPathState.PATH_FINISHED_SUCCED:
                self.generateNewInputs(currPath, statesQueue)

        print("Finished concolic !")

