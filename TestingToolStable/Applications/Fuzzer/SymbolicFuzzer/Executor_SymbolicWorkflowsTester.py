import copy
import csv
import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph
import pygraphviz as pgv
from typing import Dict, List, Set, Tuple
from z3 import *
import matplotlib as plt
from enum import Enum
import json

from Parser_WorkflowMainParser import *
from SymbolicSolverStrategies import *
from SymbolicSolverStrategies_concolic import *


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



class SymbolicWorflowsTester:
    def __init__(self,
                 baseModelPath : str,
                 testSpecFile : str,
                 strategyToUse : SymbolicSolversStrategiesTypes):
        # Create Workflow parser and all its dependencies
        self.dataStoreTemplate = DataStore() # This is the template of the data store that will be split/duplicated/reused by multiple execution branches
        self.externalFunctionsDict = DictionaryOfExternalCalls()
        self.astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(self.externalFunctionsDict)
        self.workflowExpressionParser = WorkflowExpressionsParser()

        # Change working directory to the base model path
        self.modelBasePath = baseModelPath
        os.chdir(self.modelBasePath)

        # Parse the workflow spec input and create a workflow graph instance
        self.WP = WorkflowParser(self.astFuzzerNodeExecutor, self.workflowExpressionParser)
        self.workflowGraph : WorkflowGraph = self.WP.parseWorkflows(inputPath=testSpecFile,
                                                                    astFuzzerNodeExecutor=self.astFuzzerNodeExecutor,
                                                                    dataStoreTemplate=self.dataStoreTemplate)
        self.symbolicSolverStrategy = None
        if strategyToUse == SymbolicSolversStrategiesTypes.STRATEGY_SYMBOLIC_DFS:
            self.symbolicSolverStrategy = DFSSymbolicSolverStrategy(self.workflowGraph)
        elif strategyToUse == SymbolicSolversStrategiesTypes.STRATEGY_OFFLINE_ALL:
            self.symbolicSolverStrategy = AllStatesOnesSolver(self.workflowGraph)
        elif strategyToUse == SymbolicSolversStrategiesTypes.STRATEGY_CONCOLIC:
            self.symbolicSolverStrategy = ConcolicSolverStrategy(self.workflowGraph)
        else:
            raise NotImplementedError()


    def getSolutionsOutputFilePath(self, fileName):
        return os.path.join(self.baseFolderModel, "generatedTests.csv")

    def getDebugGraphFilePath(self, fileName):
        return None if fileName is None else os.path.join(self.baseFolderModel, fileName)

    def debugGraph(self, debuggingOptions : DebuggingOptions): #= "debugGraph.png"): # Could be none
        self.workflowGraph.debugGraph(debuggingOptions)

    def solveOfflineStaticGraph(self, outputResultsFile, loggingEnabled):
        self.workflowGraph.solve(outputCsvFile=outputResultsFile, debugLogging=loggingEnabled)

    def doTests(self, args):
        # First some debugging if enabled
        self.debuggingOptions = args.debuggingOptions
        self.debugGraph(self.debuggingOptions)

        # Then invoke the strategy instance to do testing
        assert self.symbolicSolverStrategy != None, "There is no symbolic strategy instantiated ! Check your options and doc!"
        self.symbolicSolverStrategy.solve(args)

