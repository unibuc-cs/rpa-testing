from enum import Enum
from typing import List, Dict, Set
from Parser_ASTNodes import *

####################

class NodeTypes(Enum):
    BASE_NODE = 0 # Abstract, base
    FLOW_NODE = 1 # Normal node for flow, no branching
    BRANCH_NODE = 2 # Branch node

# Logic to get a debug color output depending on the name of the graph
AllDebugColors = ["red", "blue", "yellow", "green", "violet", "orange"]
NumDebugColors = len(AllDebugColors)

def getDebugColorByName(name: str) -> str:
    return AllDebugColors[(hash(name) % NumDebugColors)]

def extractVarNameFromVarPlain(varNamePlain):
    """
    Expecting a "V['name']" => name
    """
    assert varNamePlain[0] == 'V' and varNamePlain[1] == '[' and varNamePlain[-1] == "]"
    subtactVar = varNamePlain[3:-2]
    subtactVar = subtactVar.replace('\\', "")
    return subtactVar

class BaseSymGraphNode():
    def __init__(self, id : str, nodeType : NodeTypes):
        self.id = id
        self.nodeType : NodeTypes = nodeType

        # This is the node available for executor
        self.fuzzerNodeInst = None

    def __str__(self):
        return self.id #+ " " + str(self.expression)

    def isBranchNode(self) -> bool:
        return False

    def getGraphNameFromNodeId(self) -> str:
        index = self.id.find(':')
        assert index != -1, "There is no namespace for this node !"
        return str(self.id[:index])

    # Gets a debug label string to be used for this node
    def getDebugLabel(self):
        # HTML way ...maybe later
        # labelStr = f"<{nodeInst.id}<BR/><FONT POINT-SIZE=\"10\">v[add]  &gt 100 </FONT>>"

        baseOutput = self.id

        # TODO: more stuff into the new output
        """
        if self.hasAssignments():
            for assignment in self.assignments:
                baseOutput += "\n" + str(assignment.leftTerm) + " <- " + str(assignment.rightTerm)
        """
        return baseOutput

class SymGraphNodeFlow(BaseSymGraphNode):
    def __init__(self, id: str):
        super().__init__(id, NodeTypes.FLOW_NODE)
        self.nextNodeId: str = None
        self.nextNodeInst: BaseSymGraphNode = None  # Same as above but with instances

    def getDebugLabel(self):
        baseOutput = super().getDebugLabel()
        outputStr = baseOutput
        if self.expression is not None:
            if isinstance(self.expression, (ASTFuzzerNode_Assignment)):
                outputStr += "\n" + str(self.expression)
        return outputStr

# A generic branch node definition
class SymGraphNodeBranch(BaseSymGraphNode):  # Just an example of a base class
    def __init__(self, id: str):
        super().__init__(id, NodeTypes.BRANCH_NODE)
        self.expression_rawStr: str = None  # The string raw expression as defined in the config file
        self.expression: ASTFuzzerNode = None  # The parsed node expression of above
        self.valuesAndNext: Dict[str, str] = {}  # A dictionary from expression value to next branch
        self.valuesAndNextInst: Dict[str, BaseSymGraphNode] = {}  # Same as above but with inst

    def getVariables(self):
        return None  # self.expression.variables()

    def isBranchNode(self) -> bool:
        return True

    def getDebugLabel(self):
        baseOutput = super().getDebugLabel()
        outputStr = baseOutput + "\n" + str(self.expression)
        return outputStr


