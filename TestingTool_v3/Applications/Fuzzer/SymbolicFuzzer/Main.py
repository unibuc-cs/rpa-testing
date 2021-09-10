from Executor_SymbolicWorkflowsTester import *

# ---------------------------------------------------------------------------------
# How to run this script ?
"""
For a description of parameters run: python Main.py - h, or check the arguments below
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
    workflowsTester = SymbolicWorflowsTester(args.modelBasePath, args.workflowsSpecInput, args.symbolicStrategyToUse)

    if args.loggingEnabled:
        workflowsTester.debugFullGraph(outputGraphFile=args.outputGraphFile)

        # PROTO work in progress
        workflowsTester.doTests(outputResultsFile=args.outputResultsFile,
                                loggingEnabled=args.loggingEnabled, otherArgs=args)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Fuzzer process')
    parser.add_argument('-modelBasePath', type=str, help='Path to the base folder containing workflows and resources', required=True)
    parser.add_argument('-workflowsSpecInput', type=str, help='Local (from base folder) path to the json model file', required=True)
    parser.add_argument('-outputGraphFile', type=str, default="debugGraph.png", help='Path to the output debug graph file', required=True)
    parser.add_argument('-loggingEnabled', type=int, default=1, help='Verbose everything ?', required=True)
    parser.add_argument('-outputResultsFile', type=str, default="generatedests.csv", help='Path to write the output CSV file', required=True)
    parser.add_argument('-solverStrategy', type=str, default="STRATEGY_DFS", required=True) # STRATEGY_OFFLINE_ALL

    parser.add_argument('-seedsFile', type=str, default="inputSeeds.csv", required=False)
    parser.add_argument('-numRandomGeneratedSeeds', type=int, default=0, required=False)

    # Arguments processing
    args = parser.parse_args()
    args.loggingEnabled = False if args.loggingEnabled == 0 else True
    args.symbolicStrategyToUse = SymbolicSolversStrategiesTypes.from_str(args.solverStrategy)

    #args.workflowsSpecInput = os.path.join(args.modelBasePath, args.workflowsSpecInput)
    #args.outputResultsFile = os.path.join(args.modelBasePath, args.outputResultsFile)
    #args.seedsFile = os.path.join(args.modelBasePath, args.seedsFile)

    runTest(args)
    print("finished")
