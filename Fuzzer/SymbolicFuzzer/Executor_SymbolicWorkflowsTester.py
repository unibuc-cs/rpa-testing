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

class SymbolicWorflowsTester:
    def __init__(self, testSpecFile):
        self.baseFolderModel = os.path.dirname(testSpecFile)

        # Create Workflow parser and all its dependencies
        self.dataStore = DataStore()
        self.externalFunctionsDict = DictionaryOfExternalCalls()
        self.astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(self.dataStore, self.externalFunctionsDict)
        self.workflowExpressionParser = WorkflowExpressionsParser()

        # Parse the workflow spec input and create a workflow graph instance
        self.WP = WorkflowParser(self.astFuzzerNodeExecutor, self.workflowExpressionParser)
        self.workflowGraph : WorkflowGraph = self.WP.parseWorkflows(inputPath=testSpecFile, baseOutPath=self.baseFolderModel)


    def getSolutionsOutputFilePath(self, fileName):
        return os.path.join(self.baseFolderModel, "generatedTests.csv")

    def getDebugGraphFilePath(self, fileName):
        return None if fileName is None else os.path.join(self.baseFolderModel, fileName)

    def debugFullGraph(self, outputGraphFile): #= "debugGraph.png"): # Could be none
        self.workflowGraph.debugGraph(outputGraphFile=outputGraphFile)

    def solveOfflineStaticGraph(self, outputResultsFile, loggingEnabled):
        self.workflowGraph.solveOfflineStaticGraph(outputCsvFile=outputResultsFile, debugLogging=loggingEnabled)
