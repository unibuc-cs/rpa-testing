# ---------------------------------------------------------------------------------
# How to run this script ?
"""
For a description of parameters run: python Main.py - h

For a demo run use: python Main.py -testConfigFilePath "dummy_TestSpec.txt" -outputGraphFile "debugGraph.png" -outputResultsFile "generatedests.csv" -loggingEnabled 1
    What these mean ?
    the testConfigFilePath is the configuration file for the list of workflows under test.
    If you take a look at it, inside it contains the specification of the entry node, the main node name, the list of workflows files path that are involved in the process
    Each workflow description file contains the variables and graph, plus a debugging color (that is shown in the output debugGraph.png if used) and a name, which must correspond to the namespace of that workflow !

Note: In a production environment, probably you could put -loggingEnabled 0 and -outputGraphFile None
"""






# ---------------------------------------------------------------------------------
# TODO tasks:
# See the interaction graph to extend for dynamic symbolic programming and concolic
# logging support rather than printf

# First install the packages
# pip install pip install z3-solver
# pip install py_expression_eval
# pip install networkx
# pip install pygraphviz
import ast
import argparse
import os

#from py_expression_eval import Parser # Not used at the moment but might be good !
#parser = Parser()
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
from GraphDef import *


# Note: Currently, we compact all workflows in a single file and separate their nodes and variables by namespaces
# This should be ideal for our use cases...
USE_DISTRIBUTED_WORKFLOWS = False


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

class TestFactory:
    def __init__(self):
        self.baseFolderModel = None
        self.testFuzzerInstance = None
        self.mainWorkflowName = None

    def loadTestSpecFromFile(self, testSpecFile):
        with open(testSpecFile) as f:
            data = f.read()
            data = ast.literal_eval(data)

            self.debugColors = ast.literal_eval(data["debugColors"])

            self.baseFolderModel = os.path.dirname(testSpecFile)
            entryTestNodeId = data["startNode"]
            self.mainWorkflowName = data["mainWorkflowName"]

            #listOfWorkflowsPaths = data["listOfWorkflows"]
            # Put the base folder for each path as prefix

            allWorkflowsInstances : List[WorkflowDef] = []
            if USE_DISTRIBUTED_WORKFLOWS:
                listOfWorkflowsPaths = [os.path.join(self.baseFolderModel, workflowPath) for workflowPath in listOfWorkflowsPaths]
                for workflowPath in listOfWorkflowsPaths:
                    workflowInstance = self.createWorkflowSingleFromFile(workflowPath)
                    allWorkflowsInstances.append(workflowInstance)
            else: # Single compacted workflow separated by namespaces
                workflowInstance = self.createWorkflowSingleFromFile(testSpecFile)
                allWorkflowsInstances.append(workflowInstance)


            self.testFuzzerInstance = SymbolicWorflowsTester(workflows=allWorkflowsInstances,
                                                             debugColors=self.debugColors,
                                                             mainWorflowName=self.mainWorkflowName,
                                                             entryTestNodeId=entryTestNodeId)

    def getSolutionsOutputFilePath(self, fileName):
        return os.path.join(self.baseFolderModel, "generatedTests.csv")

    def getDebugGraphFilePath(self, fileName):
        return None if fileName is None else os.path.join(self.baseFolderModel, fileName)

    def debugFullGraph(self, outputGraphFile): #= "debugGraph.png"): # Could be none
        self.testFuzzerInstance.debugGraph(outputGraphFile=outputGraphFile)

    def solveOfflineStaticGraph(self, outputResultsFile, loggingEnabled):
        self.testFuzzerInstance.solveOfflineStaticGraph(outputCsvFile=outputResultsFile, debugLogging=loggingEnabled)


    def createWorkflowSingleFromFile(self, inputFilePath):
        with open(inputFilePath) as f:
            data = f.read()
            data = ast.literal_eval(data)
            variables = data["variables"]
            graph = data["graph"]
            name = data["mainWorkflowName"]

            worfklowInst = WorkflowDef(variables=variables, graph=graph, name=name, color=self.debugColors[name])
            return worfklowInst
        return None


def runTest(args):
    workflowsFactory = TestFactory()
    workflowsFactory.loadTestSpecFromFile(args.testConfigFilePath) # To do: maybe we should put these files on parameters in the end :)

    if args.loggingEnabled:
        workflowsFactory.debugFullGraph(outputGraphFile=workflowsFactory.getDebugGraphFilePath(args.outputGraphFile))

    workflowsFactory.solveOfflineStaticGraph(outputResultsFile=workflowsFactory.getSolutionsOutputFilePath(args.outputResultsFile),
                                             loggingEnabled=args.loggingEnabled)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Fuzzer process')
    parser.add_argument('-testConfigFilePath', type=str, help='Path to the config file', required=True)
    parser.add_argument('-outputGraphFile', type=str, default="debugGraph.png", help='Path to the output debug graph file', required=True)
    parser.add_argument('-loggingEnabled', type=int, default=1, help='Verbose everything ?', required=True)
    parser.add_argument('-outputResultsFile', type=str, default="generatedests.csv", help='Path to write the output CSV file', required=True)
    args = parser.parse_args()
    args.loggingEnabled = False if args.loggingEnabled == 0 else True
    runTest(args)
