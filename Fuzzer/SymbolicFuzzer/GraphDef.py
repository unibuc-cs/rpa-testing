
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

class NodeTypes(Enum):
    BASE_NODE = 0 # Abstract, base
    FLOW_NODE = 1 # Normal node for flow, no branching
    BRANCH_NODE = 2 # Branch node

class BaseNode():
    def __init__(self, id : str, nodeType : NodeTypes):
        self.id = id
        self.nodeType : NodeTypes = nodeType

    def __str__(self):
        return self.id #+ " " + str(self.expression)

    def isBranchNode(self) -> bool:
        return False

class FlowNode(BaseNode):
    def __init__(self, id : str):
        super().__init__(id, NodeTypes.FLOW_NODE)
        self.nextNodeId : str = None


# A generic branch node definition
class BranchNode(BaseNode):  # Just an example of a base class
    def __init__(self, id : str, condition : str):
        super().__init__(id, NodeTypes.BRANCH_NODE)
        self.expression = condition
        self.valuesAndNext : Dict[str, str] = {} # A dictionary from expression value to next branch

    def getVariables(self):
        return None # self.expression.variables()

    def isBranchNode(self) -> bool:
        return True

    # Functions and examples to inspect the graph at a higher level
    #-------------------------------------------------
    # A function to collect all variables by nodes
    def getAllVariables(self) -> set:
        setOfVariables = set()
        for node in self.graph.nodes:
            node = fixNodeInstance(graph, node)
            variablesInNode = node.getVariables()
            setOfVariables.update(variablesInNode)
        return setOfVariables

# An interaction point node definition
class InteractionNode(BaseNode): # TODO, work in progress
    pass