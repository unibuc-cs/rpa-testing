from Executor_SymbolicWorkflowsTester import *

# ---------------------------------------------------------------------------------
# How to run this script ?
"""
For a description of parameters run: python Main.py - h
"""

# ---------------------------------------------------------------------------------
# TODO tasks:
# logging support rather than printf

# First install the packages
# pip install pip install z3-solver
# pip install py_expression_eval
# pip install networkx
# pip install pygraphviz
import argparse
import os
from SymbolicSolverStrategies import *

def runTest(args):
    workflowsTester = SymbolicWorflowsTester(args.workflowsSpecInput, args.symbolicStrategyToUse)

    if args.loggingEnabled:
        workflowsTester.debugFullGraph(outputGraphFile=workflowsTester.getDebugGraphFilePath(args.outputGraphFile))

        # PROTO work in progress
        workflowsTester.doTests(outputResultsFile=workflowsTester.getSolutionsOutputFilePath(args.outputResultsFile),
                                loggingEnabled=args.loggingEnabled)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Fuzzer process')
    parser.add_argument('-workflowsSpecInput', type=str, help='Path to the json model file', required=True)
    parser.add_argument('-outputGraphFile', type=str, default="debugGraph.png", help='Path to the output debug graph file', required=True)
    parser.add_argument('-loggingEnabled', type=int, default=1, help='Verbose everything ?', required=True)
    parser.add_argument('-outputResultsFile', type=str, default="generatedests.csv", help='Path to write the output CSV file', required=True)
    parser.add_argument('-solverStrategy', type=str, default="STRATEGY_DFS", required=True) # STRATEGY_OFFLINE_ALL

    # Arguments processing
    args = parser.parse_args()
    args.loggingEnabled = False if args.loggingEnabled == 0 else True
    args.symbolicStrategyToUse = SymbolicSolversStrategiesTypes.from_str(args.solverStrategy)

    runTest(args)
    print("finished")
