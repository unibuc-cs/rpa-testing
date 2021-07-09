
#================
import ast
import sys
from enum import Enum
from typing import Any, List, Dict, Set
from TheNewExpressionParser_DataTypes import *
from TheNewExpressionParser_Functions import *

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

class ASTFuzzerComparator(Enum):
    COMP_LT = 1
    COMP_LTE = 2
    COMP_GT = 3
    COMP_GTE = 4


class GenericCallsParsing(ast.NodeVisitor):
    def __init__(self):
        self.names : List[str] = [] # The list of object names invoked # in the reverse order
        self.params = []

    def visit_Attribute(self, node):
        ast.NodeVisitor.generic_visit(self, node)
        self.names.append(node.attr)

    def visit_Name(self, node):
        self.names.append(node.id)

    def visit_Param(self, node):
        ast.NodeVisitor.generic_visit(self, node)
        self.params.append(node.id)


class ASTFuzzerNode:
    def __init__(self, type : ASTFuzzerNodeType):
        self.type : ASTFuzzerNodeType = type

    def isMarkerNode(self) -> bool:
        return self.type == ASTFuzzerNodeType.MARKER

class ASTFuzzerNode_VariableDecl(ASTFuzzerNode):
    """ E.g.
    "local_number_retries": {
        "Type": "Int32",
        "Default": "0"
    },
    """
    # Will put the variabile in the datastore
    def __init__(self, varName : str, typeName : str, defaultVal : str = None):
        super().__init__(ASTFuzzerNodeType.VARIABLE_DECL)
        self.typeName = typeName
        self.value = defaultVal
        self.varName = varName

        if typeName == "Int32":
            self.value = int(self.value)
        elif typeName == 'Boolean':
            self.value = False if (self.value == 'false' or self.value == 'False' or int(self.value) == 0) else True
        elif typeName == "DataTable":
            self.value = DataTable()
        elif typeName == "Float":
            pass
        else:
            raise  NotImplementedError(f"Unknown decl type {typeName}")

class ASTFuzzerNode_Marker(ASTFuzzerNode):
    def __init__(self, type : ASTFuzzerNodeType, id):
        super().__init__(ASTFuzzerNodeType.MARKER)
        self.id = id # The id of the marker

class ASTFuzzerNode_Name(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.NAME)
        self.name : str = None # A simple string name expected for something...

class ASTFuzzerNode_Attribute(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.ATTRIBUTE)
        self.names : List[str] = [] # A list of attribute names expected ???

    def addOther(self, other):
        if isinstance(other, ASTFuzzerNode_Attribute):
            self.names.extend(other.names)
        elif isinstance(other, ASTFuzzerNode_Name):
            self.names.append(other.name)
        elif isinstance(other, ASTFuzzerNode_Variable):
            self.names.append(other.variableName)
        else:
            assert False

class ASTFuzzerNode_MathUnary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.MATH_OP_UNARY)
        raise  NotImplementedError

class ASTFuzzerNode_MathBinary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.LOGIC_OP_BINARY)
        self.leftTerm : ASTFuzzerNode = None
        self.rightTerm : ASTFuzzerNode = None
        self.mathSymbol : str = None

class ASTFuzzerNode_LogicUnary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.LOGIC_OP_UNARY)
        raise  NotImplementedError

class ASTFuzzerNode_LogicBinary(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.LOGIC_OP_BINARY)
        self.leftTerm : ASTFuzzerNode = None
        self.rightTerm : ASTFuzzerNode = None
        self.logicSymbol : str = None

class ASTFuzzerNode_Variable(ASTFuzzerNode):
    def __init__(self, variableName : str):
        super().__init__(ASTFuzzerNodeType.VARIABLE)
        self.variableName = variableName

class ASTFuzzerNode_ConstantInt(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_INT)
        self.value = value

class ASTFuzzerNode_ConstantReal(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_REAL)
        self.value = value

class ASTFuzzerNode_ConstantString(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_STR)
        self.value = value

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

        assert self.comparatorClass, "No one could be set for this node !"

class ASTFuzzerNode_Compare(ASTFuzzerNode):
    def __init__(self, node :Any ):
        super().__init__(ASTFuzzerNodeType.COMPARE)

        self.comparatorClass : ASTFuzzerNode_Comparator = None
        self.leftTerm : ASTFuzzerNode = None
        self.rightTerm : ASTFuzzerNode = None

class ASTFuzzerNode_Call(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.CALL_FUNC)

        self.attributes : List[str] # The list of attributes used before call name
        self.funcCallName : str # the function being invoked by the list of attributes above
        self.args : List[ASTFuzzerNode] = [] # The argument nodes

class ASTForFuzzer:
    def __init__(self):
        self.dictOfExternalCalls : DictionaryOfExternalCalls = {}


class MainWorkflowParser(ast.NodeVisitor):
    def __init__(self):
        super().__init__()

        self.MAX_STACK_SIZE = 1000

        # The current stack of nodes beings parsed
        self.currentNodesStack : List[ASTFuzzerNode] = [None]*self.MAX_STACK_SIZE

        # The current location for beggining of the current parsing stack
        #self.currentMarkerIndex = 0

        # Where to write next on stack
        self.currentMarkerHead = 0

        # How many expression count do we expect
        self.expectedNumExpressions = None

    def stackNode(self, node : ASTFuzzerNode):
        assert self.currentMarkerHead < self.MAX_STACK_SIZE, "end of stack.."
        self.currentNodesStack[self.currentMarkerHead] = node
        self.currentMarkerHead += 1

    def popNode(self) -> ASTFuzzerNode:
        assert  self.currentMarkerHead >= 1
        self.currentMarkerHead -= 1
        res = self.currentNodesStack[self.currentMarkerHead]
        return res

    def peekTopNode(self) -> ASTFuzzerNode:
        if self.currentMarkerHead < 1:
            return None
        return self.currentNodesStack[self.currentMarkerHead-1] # Return top node

    def tryPopMarker(self, expectedMarkerId):
        marker = self.popNode()
        assert marker.isMarkerNode() and marker.id == expectedMarkerId, "incorrect node marker check"

    def pushStartMarker(self) -> int: # Returns the marker id node
        markerNodeId = self.currentMarkerHead
        markerNode = ASTFuzzerNode_Marker(ASTFuzzerNodeType.MARKER, id=markerNodeId ) # Use the head as id...
        self.stackNode(markerNode)
        return markerNodeId

    # Get the evaluated nodes list
    def getFinalOutput(self) -> List[ASTFuzzerNode]:
        assert self.currentMarkerHead == self.expectedNumExpressions + 1, "The stack should contain at least the head marker plus one or more nodes for each expression in the body"
        assert self.currentNodesStack[0].isMarkerNode()
        return self.currentNodesStack[1:1+self.expectedNumExpressions]

    def visit_Compare(self, node : ast.Compare):
        markerId = self.pushStartMarker()

        # Parse the node elements
        self.visit(node.left)
        self.stackNode(ASTFuzzerNode_Comparator(node.ops[0]))
        self.visit(node.comparators[0])

        # Now pop the needed element from stack and fill them.
        rightTerm = self.popNode()
        compTerm = self.popNode()
        leftTerm = self.popNode()
        self.tryPopMarker(markerId)

        # expected semantic: marker + leftTerm + comparator + rightTerm
        compareNode = ASTFuzzerNode_Compare(ASTFuzzerNodeType.COMPARE)
        compareNode.leftTerm = leftTerm
        compareNode.rightTerm = rightTerm
        compareNode.comparatorClass = compTerm


        # Get back and fill the compare node
        self.stackNode(compareNode)

    def visit_Expr(self, node: ast.Expr) -> Any:
        self.visit(node.value)

    def visit_Module(self, node : ast.Module):
        markerId = self.pushStartMarker()

        assert self.expectedNumExpressions == None, "You already filtered a node with this parser. REset or check !"

        # Parse each body expression
        assert isinstance(node.body, list)
        self.expectedNumExpressions = len(node.body)

        for exprNode in node.body:
            assert isinstance(exprNode, ast.Expr)
            self.visit(exprNode)

        #self.tryPopMarker(markerId)

    # CHECK #########
    def visit_Attribute(self, node : ast.Attribute):
        markerId = self.pushStartMarker()
        ast.NodeVisitor.generic_visit(self, node)

        # Expecting a stack of [name, marker, ...name,marker, ...and so one for each attribute being invoked]

        attrNode = ASTFuzzerNode_Attribute()

        # Extract all nodes until the marker sent as attributes
        while True:
            topNode = self.peekTopNode()
            if topNode is None:
                break
            nodeOnStack = self.popNode()
            attrNode.addOther(nodeOnStack)
            self.tryPopMarker(markerId)
            break

        attrNode.names.append(node.attr)
        self.stackNode(attrNode)

    def visit_Name(self, node : ast.Name):
        nameNode = ASTFuzzerNode_Name()
        nameNode.name = node.id
        self.stackNode(nameNode)

    # CHECK END #########

    def visit_Call(self, node):
        markerId = self.pushStartMarker()

        funcCallNode = ASTFuzzerNode_Call()

        # Get the list of names used
        self.visit(node.func)

        # At this point we expect a list of attributes + function name, attributes could be empty
        while True:
            topNode = self.peekTopNode()
            if topNode is None:
                assert False , "Unexpected end "
            if topNode.isMarkerNode() :
                assert False, "unexpected marker node"
            if isinstance(topNode, ASTFuzzerNode_Name):
                nameNode : ASTFuzzerNode_Name = self.popNode()
                funcCallNode.funcCallName = nameNode.name
                funcCallNode.attributes = []
            elif isinstance(topNode, ASTFuzzerNode_Attribute):
                attrNode : ASTFuzzerNode_Attribute = self.popNode()
                funcCallNode.funcCallName = attrNode.names[-1]
                funcCallNode.attributes = attrNode.names[:-1]
            else:
                assert False ,"Unkown case"
            break

        funcCallNode.args = []

        for funcArg in node.args:
            self.visit(funcArg)
            topNode = self.popNode()
            assert topNode == None or topNode.isMarkerNode() is False, "Invalid expected argument node parsed"
            funcCallNode.args.append(topNode)

        self.tryPopMarker(markerId)

        self.stackNode(funcCallNode)

        #p = GenericCallsParsing()
        #p.visit(node.func)

        #out_text = f"Attributes: {p.names[:-1]} | CallName = {p.names[-1]} | Params = {p.params}"
        #print(out_text)
        #ast.NodeVisitor.generic_visit(self, node)
        #p.visit(node.args)

    def visit_Num(self, node: ast.Num) -> Any:
        constantNum = ASTFuzzerNode_ConstantInt(node.n)
        self.stackNode(constantNum)

    def visit_Name(self, node: ast.Name) -> Any:
        nameVar = ASTFuzzerNode_Variable(node.id)
        self.stackNode(nameVar)

    def visit_Assign(self, node: ast.Assign) -> Any:
        pass

    def visit_And(self, node: ast.And) -> Any:
        pass


# Data store to handle variables management, either static, dynamic, symbolic, etc
class DataStore:
    def __init__(self):
        self.Values : Dict[str, any] = {}
        self.Types : Dict[str, str] = {}

    # Sets an existing variable value
    def setVariableValue(self, varName, value):
        assert varName in self.Values
        self.Values[varName] = value

    # ADds a variabile
    def addVariable(self, varDecl : ASTFuzzerNode_VariableDecl):
        assert varDecl.varName not in self.Values and varDecl.varName not in self.Types
        self.Values[varDecl.varName] = varDecl.value
        self.Types[varDecl.typeName] = varDecl.typeName

    # Retrieve the value of a variable
    def getVariableValue(self, varName) -> any:
        return self.Values[varName]

# This class will be responsible for the execution of ASTFuzzer nodes
class ASTFuzzerNodeExecutor:
    def __init__(self, DS : DataStore):
        self.DS = DS

    def executeNode(self, node : ASTFuzzerNode):
        if isinstance(node, ASTFuzzerNode_Call):
            args : List[ASTFuzzerNode] = node.args
            funcName : str = node.funcCallName
            attributes : List[str] = node.attributes
            args_values = [self.executeNode(argNode) for argNode in args]

            # We have a sequence of attributes, so we must check what are the types behind first
            if len(attributes) > 0:
                pass
            else:
                pass
        elif isinstance(node, ASTFuzzerNode_VariableDecl):
            self.DS.addVariable(node)
            return None
        elif isinstance(node, list):
            for exprNode in node:
                self.executeNode(exprNode)
        else:
            raise NotImplementedError("This is not supported yet")


def unitTest1():
    DS = DataStore()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(DS)

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="myStr", typeName='Int32', defaultVal="123")
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Test code: Convert it to string, then to integer, then to float
    code_block = "float.Parse(Int32.Parse(varName.ToString()))"
    code_block = ast.parse(code_block)

    ourMainWorkflowParser = MainWorkflowParser()
    ourMainWorkflowParser.visit(code_block)
    result: List[ASTFuzzerNode] = ourMainWorkflowParser.getFinalOutput()


    res = astFuzzerNodeExecutor.executeNode(result)

def unitTest2():
    # TODO: table test
    pass


if __name__ == '__main__':
    unitTest1()
    unitTest2()
    sys.exit(0)

    """
    code = "Item(0)" #"Int32.Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"  #'something = a.b.method(foo() + xtime.time(), var=1) + q.y(x.m())' # 'something = a.b.method(foo() + xtime.time(), var=1) + q.y(x.m())'
    tree = ast.parse(code)
    ParseFunctionsVisitor().visit(tree)
    """

    code_1 = "local_number_retries < 3 \n  "
    code_2 = "loan >= 1000 and loan < 100000"
    code_3 = "local_number_retries = local_number_retries + 1"

    code_31 = "obtained_result = loan_type + \" \" + term_type"

    code_4 = "actual_pin_values.ElementAt(local_number_retries) = expected_pin"
    code_5 = "Int32.Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"
    code_5 = "local_test_data.Rows.Item(0).Item2(1)"
    codeTree2 = ast.parse(code_5)


    #code_5 = "Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"

    code = code_5
    codeTree = ast.parse(code)
    ourMainWorkflowParser = MainWorkflowParser()
    ourMainWorkflowParser.visit(codeTree)
    result: List[ASTFuzzerNode] = ourMainWorkflowParser.getFinalOutput()
    print(result)

    sys.exit(0)
