# TODO tasks:
# See the interaction graph to extend for dynamic symbolic programming and concolic
# logging support rather than printf

# First install the packages
# pip install pip install z3-solver
# pip install py_expression_eval
# pip install networkx
# pip install pygraphviz


from py_expression_eval import Parser # Not used at the moment but might be good !
parser = Parser()
import copy
import csv
import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout, to_agraph
import pygraphviz as pgv
from typing import Dict, List, Set, Tuple
from z3 import *
import matplotlib as plt
from enum import Enum

from GraphDef import *


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

def demo_bankLoanExample():

    # Workflow 1: the bank loan main (embedding a PIN test grpah inside)
    # Check the rules for embedding as written below in comments
    variables_bankLoanMainGraph = {'Main:loan' : 'Real', 'Main:term' : 'Int', 'Main:context_userId' : ('Context', 2, 'Int')}

    bankLoanMainGraph = {'Main:node_loanTest0' : ('V["Main:loan"] < 1000', [('True', 'Main:lowVolumeLoan'), ('False', 'Main:node_loanTest1')]),
                     'Main:lowVolumeLoan' : (None, 'Main:term_test0'),
                    'Main:node_loanTest1' : ('And(V["Main:loan"] >= 1000, V["Main:loan"] < 100000)', [('True', 'Main:midVolumeLoan'), ('False', 'Main:highVolumeLoan')]),
                    'Main:lowVolumeLoan' : (None, 'Main:term_test0'),
                     'Main:midVolumeLoan' : (None, 'Main:term_test0'),
                    'Main:highVolumeLoan' : (None, 'Pin:checkPin'),

                    'Pin:FailedCheck' : (None, 'Main:fail'), # These 2 nodes will not be created inside this graph ! Only the links will be created
                    'Pin:SucceedCheck' : (None, 'Main:term_test0'),

                    'Main:term_test0' : ('V["Main:term"] < 5', [('True', 'Main:shortTermLoan'), ('False', 'Main:longTermLoan')]),
                    'Main:shortTermLoan' :  (None, 'Main:outputRate'),
                    'Main:longTermLoan': (None, 'Main:outputRate'),
                     'Main:outputRate' : (None, None),
                    'Main:fail' : (None, 'Main:node_loanTest0')
                    }

    bankLoanWorkflow = WorkflowDef(variables=variables_bankLoanMainGraph, graph=bankLoanMainGraph, name="Main", color='red')


    # The second workflow definition
    variables_bankPinTest = {'Pin:local_pinCorrect' : ('Context', False, 'Bool'), 'Pin:local_numberRetries' : ('Context', 0, 'Int')}
    # Notes:    - checkPin node should write local_piCorrect to either true or false and increase the local_nu
    #           - retryFailed should increment the local_numberRetries
    bankPinTest = { 'Pin:checkPin' : (None, 'Pin:pinTest0'),
                    'Pin:pinTest0' : ('V["Pin:local_pinCorrect"] == True', [('True', 'Pin:SucceedCheck'), ('False', 'Pin:retryFailed')]),
                     'Pin:retryFailed' : (None, 'Pin:checkRetryTest'),
                    'Pin:checkRetryTest' : ('V["Pin:local_numberRetries"] < 3', [('True', 'Pin:checkPin'), ('False', 'Pin:FailedCheck')]),
                     'Pin:SucceedCheck' : (None, None),
                     'Pin:FailedCheck' : (None, None),
                     }

    bankPinWorkflow = WorkflowDef(variables=variables_bankPinTest, graph=bankPinTest, name = "Pin", color='blue')

    allWorkflows : List[WorkflowDef] = [bankPinWorkflow, bankLoanWorkflow]
    testFuzzer = SymbolicWorflowsTester(workflows=allWorkflows, mainWorflowName=bankLoanWorkflow.name, entryTestNodeId='Main:node_loanTest0')
    testFuzzer.debugGraph(outputGraphFile="debugGraph.png")
    testFuzzer.solveOfflineStaticGraph(outputCsvFile="generatedTests.csv", debugLogging=False)


if __name__ == "__main__":
    # Creating the graph now from a given dictionary
    demo_bankLoanExample()

    # TODO and usecases:
    #   -   demo with foreach
    #   -   interaction node usage
    #   -   others

