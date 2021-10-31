from enum import Enum
from typing import List, Dict, Set, Any
from Parser_DataTypes import *
#from SymbolicHelpers import *
import ast

#================

class ASTFuzzerNodeType(Enum):
    NOT_SET = 0
    LOGIC_OP_BINARY = 1
    LOGIC_OP_UNARY = 2
    MATH_OP_BINARY = 3
    MATH_OP_UNARY = 4
    CALL_FUNC = 5
    CONSTANT_STR = 6
    CONSTANT_INT = 7
    CONSTANT_REAL = 8
    VARIABLE = 9
    COMPARATOR = 10
    COMPARE = 11
    ATTRIBUTE = 12
    NAME=13
    MARKER = 14
    VARIABLE_DECL = 15
    ASSIGNMENT = 16
    KEYWORD_PARAM = 17
    DICT = 18
    CONSTANT_BOOL = 19
    FOREACH_ITERATION = 20
    SUBSCRIPT = 21


class ASTFuzzerComparator(Enum):
    COMP_LT = 1
    COMP_LTE = 2
    COMP_GT = 3
    COMP_GTE = 4
    COMP_EQ = 5
    COMP_NOTEQ = 6


def ASTFuzzerComparatorToStr(compOp: ASTFuzzerComparator) -> str:
    if compOp == ASTFuzzerComparator.COMP_LT:
        return "<"
    elif compOp == ASTFuzzerComparator.COMP_GT:
        return ">"
    elif compOp == ASTFuzzerComparator.COMP_LTE:
        return "<="
    elif compOp == ASTFuzzerComparator.COMP_GTE:
        return ">="
    elif compOp == ASTFuzzerComparator.COMP_EQ:
        return "=="
    elif compOp == ASTFuzzerComparator.COMP_NOTEQ:
        return "!="
    else:
        raise NotImplementedError("Unknwon type")
        return None


    #  Base class for all nodes
class ASTFuzzerNode:
    def __init__(self, type : ASTFuzzerNodeType):
        self.type : ASTFuzzerNodeType = type

    def isMarkerNode(self) -> bool:
        return self.type == ASTFuzzerNodeType.MARKER

    # returns true if there is any symbolic variabile inside the node
    def isAnySymbolicVar(self, contextDataStore) -> bool:
        raise NotImplementedError() # Base class not


class ASTFuzzerNode_Assignment(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.ASSIGNMENT)
        self.leftTerm: ASTFuzzerNode = None
        self.rightTerm: ASTFuzzerNode = None

    def __str__(self):
        if isinstance(self.rightTerm, (List, Set)):
            res = f"{self.leftTerm} = ["
            numItems = len(self.rightTerm)
            for rightIndex, rightVal in enumerate(self.rightTerm):
                res += str(rightVal)
                if rightIndex < numItems - 1:
                    res += ", "
                else:
                    res += "]"
        else:
            res = f"{self.leftTerm} = {self.rightTerm}"
        return res

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.leftTerm.isAnySymbolicVar(contextDataStore) or self.rightTerm.isAnySymbolicVar(contextDataStore)



USE_WORKFLOWNAME_BEFORE_VARIABLE = True # WorkflowName:VariableName in expressions or just VariableName ?


# Attribute data.
class AttributeData:
    def __init__(self, node : ASTFuzzerNode, name : str, subscriptNode = None):
        self.node = node
        self.name = name
        self.subscript : ASTFuzzerNode_Subscript = subscriptNode

        # We recursively try to find out the name of the last attribute that is using one or more subscripts eg. datatable.rows[row_index][column_index]
        if self.subscript:
            currNode = self.subscript.valueNode
            while currNode is not None and isinstance(currNode, AttributeData) and currNode.subscript != None:
                currNode = currNode.subscript.valueNode

            if isinstance(currNode, ASTFuzzerNode_Subscript):
                validName = currNode.valueNode.listOfAttributesData[-1].name
            else:
                validName = currNode.name
            self.name = validName

    # returns true if there is any symbolic variabile inside the node
    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.node.isAnySymbolicVar(contextDataStore) or (self.subscript != None and self.subscript.isAnySymbolicVar(contextDataStore))

    def __str__(self):
        res = str(self.subscript) if self.subscript is not None else self.name
        return res


class ASTFuzzerNode_Marker(ASTFuzzerNode):
    def __init__(self, type : ASTFuzzerNodeType, id):
        super().__init__(ASTFuzzerNodeType.MARKER)
        self.id = id # The id of the marker

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        raise NotImplementedError() # Not needed

class ASTFuzzerNode_Name(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.NAME)
        self.name : str = None # A simple string name expected for something...

    # returns true if there is any symbolic variabile inside the node
    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return contextDataStore.isVariableSymbolic(self.name)

class ASTFuzzerNode_Attribute(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.ATTRIBUTE)
        self.listOfAttributesData : List[AttributeData] = [] # A list of attribute names expected ???

    def addOther(self, other):
        if isinstance(other, ASTFuzzerNode_Attribute):
            self.listOfAttributesData.extend(other.listOfAttributesData)
        elif isinstance(other, ASTFuzzerNode_Name):
            self.listOfAttributesData.append(AttributeData(node=other, name=other.name))
        elif isinstance(other, ASTFuzzerNode_Variable):
            self.listOfAttributesData.append(AttributeData(node=other, name=other.name))
        elif isinstance(other, ASTFuzzerNode_Call):
            self.listOfAttributesData.append(AttributeData(node=other, name=other.funcCallName))
        elif isinstance(other, ASTFuzzerNode_Subscript):
            self.listOfAttributesData.append(AttributeData(node=None, name=None, subscriptNode=other))
        else:
            assert False

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        for x in self.listOfAttributesData:
            if x.isAnySymbolicVar(contextDataStore):
                return True
        return False

    def __str__(self):
        res = ""
        for x in self.listOfAttributesData:
            res += str(x)
            if x != self.listOfAttributesData[-1]:
                res += "."
        return res

class ASTFuzzerNode_KeywordParam(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.KEYWORD_PARAM)
        self.paramName : Union[None, str] = None
        self.paramNode: Union[None, ASTFuzzerNode] = None

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.paramNode.isAnySymbolicVar(contextDataStore)

class ASTFuzzerNode_MathUnary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.MATH_OP_UNARY)
        raise  NotImplementedError

class ASTFuzzerNode_MathBinary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.MATH_OP_BINARY)
        self.leftTerm : ASTFuzzerNode = None
        self.rightTerm : ASTFuzzerNode = None
        self.op : str = None

    def __str__(self):
        res = f"{self.leftTerm} {self.op} {self.rightTerm}"
        return res

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.leftTerm.isAnySymbolicVar(contextDataStore) or self.rightTerm.isAnySymbolicVar(contextDataStore)

class ASTFuzzerNode_LogicUnary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.LOGIC_OP_UNARY)
        raise  NotImplementedError

class ASTFuzzerNode_LogicBinary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.LOGIC_OP_BINARY)
        self.leftTerm : ASTFuzzerNode = None
        self.rightTerm : ASTFuzzerNode = None
        self.op : str = None

    def __str__(self):
        res = f"{self.leftTerm} {self.op} {self.rightTerm}"
        return res

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.leftTerm.isAnySymbolicVar(contextDataStore) or self.rightTerm.isAnySymbolicVar(contextDataStore)

class ASTFuzzerNode_Variable(ASTFuzzerNode):
    def __init__(self, variableName : str):
        super().__init__(ASTFuzzerNodeType.VARIABLE)
        self.name = f"{ASTFuzzerNode.currentWorkflowNameParsed}:{variableName}" if USE_WORKFLOWNAME_BEFORE_VARIABLE else variableName

    def __str__(self):
        return str(self.name)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return contextDataStore.isVariableSymbolic(self.name)

class ASTFuzzerNode_ConstantInt(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_INT)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return False

class ASTFuzzerNode_ConstantBool(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_BOOL)
        self.value = bool(value)

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return False

class ASTFuzzerNode_ConstantReal(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_REAL)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return False

class ASTFuzzerNode_ConstantString(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_STR)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return False

class ASTFuzzerNode_Dict(ASTFuzzerNode):
    def __init__(self, value : Dict):
        super().__init__(ASTFuzzerNodeType.DICT)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return False

class ASTFuzzerNode_Comparator(ASTFuzzerNode):
    def __init__(self, node :Any ):
        super().__init__(ASTFuzzerNodeType.COMPARATOR)

        self.comparatorClass = None
        if isinstance(node, ast.Lt):
            self.comparatorClass = ASTFuzzerComparator.COMP_LT
        elif isinstance(node, ast.LtE):
            self.comparatorClass = ASTFuzzerComparator.COMP_LTE
        elif isinstance(node, ast.GtE):
            self.comparatorClass = ASTFuzzerComparator.COMP_GTE
        elif isinstance(node, ast.Gt):
            self.comparatorClass = ASTFuzzerComparator.COMP_GT
        elif isinstance(node, ast.Eq):
            self.comparatorClass = ASTFuzzerComparator.COMP_EQ
        elif isinstance(node, ast.NotEq):
            self.comparatorClass = ASTFuzzerComparator.COMP_NOTEQ

        assert self.comparatorClass, "No one could be set for this node !"

    def __str__(self):
        return ASTFuzzerComparatorToStr(self.comparatorClass)

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return False


class ASTFuzzerNode_Compare(ASTFuzzerNode):
    def __init__(self, node :Any ):
        super().__init__(ASTFuzzerNodeType.COMPARE)

        self.comparatorClassNode : ASTFuzzerNode_Comparator = None
        self.leftTerm : ASTFuzzerNode = None
        self.rightTerm : ASTFuzzerNode = None

    def __str__(self):
        res = f"{self.leftTerm} {self.comparatorClassNode} {self.rightTerm}"
        return res

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.leftTerm.isAnySymbolicVar(contextDataStore) or self.rightTerm.isAnySymbolicVar(contextDataStore)

class ASTFuzzerNode_Subscript(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.SUBSCRIPT)

        self.valueNode : ASTFuzzerNode = None
        self.sliceNode : ASTFuzzerNode = None  # value[slice] node

    def __str__(self):
        res = f"{self.valueNode}[{self.sliceNode}]"
        return res

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        return self.valueNode.isAnySymbolicVar(contextDataStore) or self.sliceNode.isAnySymbolicVar(contextDataStore)


class ASTFuzzerNode_Call(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.CALL_FUNC)

        self.attributes : List[AttributeData] # The list of attributes used before call name
        self.funcCallName : str # the function being invoked by the list of attributes above
        self.args : List[ASTFuzzerNode] = [] # The argument nodes
        self.kwargs : Dict[str, ASTFuzzerNode] = {} # The kwargs stuff

    def __str__(self):
        res = ""
        # Put attributes up to the function call
        for attr in self.attributes:
            res += str(attr)
            res += "."

        # Put func call name
        res += self.funcCallName + "("

        # Then the parameter
        for argIndex, argValue in enumerate(self.args):
            res += str(argValue)
            if argIndex < len(self.args) - 1:
                res += ","
        res += ")"

        return res

    def isAnySymbolicVar(self, contextDataStore) -> bool:
        for argIndex, argValue in enumerate(self.args):
            if argValue.isAnySymbolicVar(contextDataStore):
                return True

        return True

class ASTForFuzzer:
    def __init__(self):
        self.dictOfExternalCalls : DictionaryOfExternalCalls = {}

class ASTFuzzerNode_FOREACH(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.FOREACH_ITERATION)
        self.iteratedObject_node: ASTFuzzerNode = None
        self.iteratedVar_node: ASTFuzzerNode = None
        self.originalExpression : str = None

    def __str__(self):
        return self.originalExpression
