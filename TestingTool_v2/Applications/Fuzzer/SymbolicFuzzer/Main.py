from Executor_SymbolicWorkflowsTester import *

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
# logging support rather than printf

# First install the packages
# pip install pip install z3-solver
# pip install py_expression_eval
# pip install networkx
# pip install pygraphviz
import ast
import argparse
import os

def runTest(args):
    workflowsTester = SymbolicWorflowsTester(args.workflowsSpecInput)


    if args.loggingEnabled:
        workflowsTester.debugFullGraph(outputGraphFile=workflowsTester.getDebugGraphFilePath(args.outputGraphFile))

    if True:
        workflowsTester.solveOfflineStaticGraph(outputResultsFile=workflowsTester.getSolutionsOutputFilePath(args.outputResultsFile),
                                                 loggingEnabled=args.loggingEnabled)
    else:
        # PROTO work in progress
        workflowsTester.solveSymbolically(outputResultsFile=workflowsTester.getSolutionsOutputFilePath(args.outputResultsFile),
                                            loggingEnabled=args.loggingEnabled)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Fuzzer process')
    parser.add_argument('-workflowsSpecInput', type=str, help='Path to the config file', required=True)
    parser.add_argument('-outputGraphFile', type=str, default="debugGraph.png", help='Path to the output debug graph file', required=True)
    parser.add_argument('-loggingEnabled', type=int, default=1, help='Verbose everything ?', required=True)
    parser.add_argument('-outputResultsFile', type=str, default="generatedTests.csv", help='Path to write the output CSV file', required=True)
    args = parser.parse_args()
    args.loggingEnabled = False if args.loggingEnabled == 0 else True
    runTest(args)
