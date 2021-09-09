# THis is workflow expression parser purpose script, using AST

#================
import ast
import sys
import re
from enum import Enum
from typing import Any, List, Dict, Set, Tuple, Union
from Parser_DataTypes import *
from Parser_Functions import *
from SymbolicHelpers import *

USE_WORKFLOWNAME_BEFORE_VARIABLE = True # WorkflowName:VariableName in expressions or just VariableName ?



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
    def isAnySymbolicVar(self) -> bool:
        raise NotImplementedError() # Base class not


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
    def isAnySymbolicVar(self) -> bool:
        return self.node.isAnySymbolicVar() or (self.subscript != None and self.subscript.isAnySymbolicVar())

    def __str__(self):
        res = str(self.subscript) if self.subscript is not None else self.name
        return res


class ASTFuzzerNode_VariableDecl(ASTFuzzerNode):
    """ E.g.
    "local_number_retries": {
        "Type": "Int32",
        "Default": "0"
    },
    """

    # Given the type of the variable as a string and the expression containing the default value, get the default object value
    @staticmethod
    def getDefaultValueFromExpression(varTypeName: str, defaultExpression: str) -> any:
        res = None
        if varTypeName == "Int32":
            res = 0 if defaultExpression is None else int(defaultExpression)
        elif varTypeName == 'Boolean':
            res = False if (defaultExpression == None or defaultExpression == 'false' or defaultExpression == 'False'
                  or int(defaultExpression) == 0) else True
        elif varTypeName == 'Dictionary<string,int32>':
            res = Dictionary()
        elif varTypeName == 'String':
            res = str(defaultExpression)
        elif varTypeName == 'Dictionary`2':
            res = Dictionary()
        else:
            raise NotImplementedError("Do it yourself !!")

        return res


    # Will put the variabile in the datastore
    def __init__(self, varName : str, typeName : str, **kwargs):
        super().__init__(ASTFuzzerNodeType.VARIABLE_DECL)
        self.typeName = typeName
        self.defaultValue = kwargs['defaultValue'] if 'defaultValue' in kwargs else None
        self.varName = varName

        # self.value represents the CURRENT concrete value, while self.symbolicValue represents the Z3 symbolic value associated with it
        self.symbolicValue = None
        self.value = None

        # Fill the annotations
        self.annotation = VarAnnotation()
        annotationTag = kwargs.get('annotation')
        if annotationTag is not None:
            if 'bounds' in annotationTag:
                self.annotation.bounds = int(annotationTag['bounds'])
            if 'min' in annotationTag:
                self.annotation.min = int(annotationTag['min'])
            if 'max' in annotationTag:
                self.annotation.max = int(annotationTag['max'])
            if 'pattern' in annotationTag:
                self.annotation.pattern = str(annotationTag['pattern'])
            if 'userInput' in annotationTag:
                valSpec = annotationTag['userInput']
                self.annotation.isFromUserInput = 1 if (valSpec == 'True' or valSpec == '1' or valSpec == 'true') else 0
                if self.annotation.isFromUserInput == 1:
                    assert self.defaultValue == None, "In the case of variables coming as inputs you can't put a default value !"

        # Build the variabile symbolic and default value depending on its type
        if typeName == "Int32":
            self.value = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName=typeName,
                                                                                  defaultExpression=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)

        elif typeName == 'Int32[]':
            self.value = FuzzerArray.CreateArray('Int32', annotation=self.annotation, defaultValue=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == 'String[]':
            self.value = FuzzerArray.CreateArray('String', annotation=self.annotation, defaultValue=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == "List":
            assert self.annotation is None or self.annotation.isFromUserInput is False, \
                "List type is not supported for symbolic execution since its element could be anything !!. So no annotation please that involves symbolic"

            self.value = FuzzerList.Create(annotation=self.annotation, defaultValue=self.defaultValue)

        elif typeName == 'Boolean':
            self.value = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName=typeName,
                                                                                  defaultExpression=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == "DataTable":
            lazyLoad = True if 'lazyLoad' not in kwargs else kwargs['lazyLoad']
            path = self.defaultValue
            self.value = DataTable(path=path, lazyLoad=lazyLoad)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)

        elif typeName == "DataTable_iterator":
            assert self.defaultValue, "You must specify a default value in this case"

            self.value = self.defaultValue
        elif typeName == "String":
            self.value = str(self.defaultValue) if self.defaultValue == None else ""

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == "Float":
            raise NotImplementedError("Not yet")
        elif typeName == "Dictionary<string,int32>":
            self.value = Dictionary()
        elif typeName == "Dictionary`2":
            self.value = Dictionary()
        else:
            raise  NotImplementedError(f"Unknown decl type {typeName}")

class ASTFuzzerNode_Marker(ASTFuzzerNode):
    def __init__(self, type : ASTFuzzerNodeType, id):
        super().__init__(ASTFuzzerNodeType.MARKER)
        self.id = id # The id of the marker

    def isAnySymbolicVar(self) -> bool:
        raise NotImplementedError() # Not needed

class ASTFuzzerNode_Name(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.NAME)
        self.name : str = None # A simple string name expected for something...

    # returns true if there is any symbolic variabile inside the node
    def isAnySymbolicVar(self) -> bool:
        return ASTFuzzerNode.dataStore.isVariableSymbolic(self.name)

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

    def isAnySymbolicVar(self) -> bool:
        for x in self.listOfAttributesData:
            if x.isAnySymbolicVar():
                return True
        return False

    def __str__(self):
        res = ""
        for x in self.listOfAttributesData:
            res += str(x)
            if x != self.listOfAttributesData[-1]:
                res += "."
        return res

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

    def isAnySymbolicVar(self) -> bool:
        return self.leftTerm.isAnySymbolicVar() or self.rightTerm.isAnySymbolicVar()

class ASTFuzzerNode_KeywordParam(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.KEYWORD_PARAM)
        self.paramName : Union[None, str] = None
        self.paramNode: Union[None, ASTFuzzerNode] = None

    def isAnySymbolicVar(self) -> bool:
        return self.paramNode.isAnySymbolicVar()

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

    def isAnySymbolicVar(self) -> bool:
        return self.leftTerm.isAnySymbolicVar() or self.rightTerm.isAnySymbolicVar()

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

    def isAnySymbolicVar(self) -> bool:
        return self.leftTerm.isAnySymbolicVar() or self.rightTerm.isAnySymbolicVar()

class ASTFuzzerNode_Variable(ASTFuzzerNode):
    def __init__(self, variableName : str):
        super().__init__(ASTFuzzerNodeType.VARIABLE)
        self.name = f"{ASTFuzzerNode.currentWorkflowNameParsed}:{variableName}" if USE_WORKFLOWNAME_BEFORE_VARIABLE else variableName

    def __str__(self):
        return str(self.name)

    def isAnySymbolicVar(self) -> bool:
        return ASTFuzzerNode.dataStore.isVariableSymbolic(self.name)

class ASTFuzzerNode_ConstantInt(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_INT)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self) -> bool:
        return False

class ASTFuzzerNode_ConstantBool(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_BOOL)
        self.value = bool(value)

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self) -> bool:
        return False

class ASTFuzzerNode_ConstantReal(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_REAL)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self) -> bool:
        return False

class ASTFuzzerNode_ConstantString(ASTFuzzerNode):
    def __init__(self, value : str):
        super().__init__(ASTFuzzerNodeType.CONSTANT_STR)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self) -> bool:
        return False

class ASTFuzzerNode_Dict(ASTFuzzerNode):
    def __init__(self, value : Dict):
        super().__init__(ASTFuzzerNodeType.DICT)
        self.value = value

    def __str__(self):
        return str(self.value)

    def isAnySymbolicVar(self) -> bool:
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

    def isAnySymbolicVar(self) -> bool:
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

    def isAnySymbolicVar(self) -> bool:
        return self.leftTerm.isAnySymbolicVar() or self.rightTerm.isAnySymbolicVar()

class ASTFuzzerNode_Subscript(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.SUBSCRIPT)

        self.valueNode : ASTFuzzerNode = None
        self.sliceNode : ASTFuzzerNode = None  # value[slice] node

    def __str__(self):
        res = f"{self.valueNode}[{self.sliceNode}]"
        return res

    def isAnySymbolicVar(self) -> bool:
        return self.valueNode.isAnySymbolicVar() or self.sliceNode.isAnySymbolicVar()


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

    def isAnySymbolicVar(self) -> bool:
        for argIndex, argValue in enumerate(self.args):
            if argValue.isAnySymbolicVar():
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

WorkflowCodeBlockParsed = List[ASTFuzzerNode]

class WorkflowExpressionsParser(ast.NodeVisitor):
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
        compareNode.comparatorClassNode = compTerm


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
            assert isinstance(exprNode, ast.Expr) or isinstance(exprNode, ast.Assign)
            self.visit(exprNode)

        #self.tryPopMarker(markerId)

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        markerId = self.pushStartMarker()

        # Create the subscript node
        resNode = ASTFuzzerNode_Subscript()
        self.visit(node.value)
        resNode.valueNode = self.popNode()

        self.visit(node.slice)
        resNode.sliceNode = self.popNode()

        self.tryPopMarker(markerId)

        # And stack it
        self.stackNode(resNode)

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

        attrNode.listOfAttributesData.append(AttributeData(node=attrNode, name=node.attr))
        self.stackNode(attrNode)

    def visit_Name(self, node : ast.Name):
        nameNode = ASTFuzzerNode_Name()
        nameNode.name = node.id
        self.stackNode(nameNode)

    def visit_Str(self, node: ast.Str) -> Any:
        strConstantNode = ASTFuzzerNode_ConstantString(node.s)
        strConstantNode.value = node.s
        self.stackNode(strConstantNode)

    def visit_Dict(self, node: Dict) -> Any:
        markerId = self.pushStartMarker()

        dictRes = {}

        # For each key and data parse them and fill in the dict
        for keyIndex, keyNodeData in enumerate(node.keys):
            # Visit the key
            self.visit(keyNodeData)
            nodeKey = self.popNode()

            # Visit the data value
            nodeValueData = node.values[keyIndex]
            self.visit(nodeValueData)
            nodeValue = self.popNode()

            dictRes[nodeKey.value] = nodeValue
        self.tryPopMarker(markerId)

        res = ASTFuzzerNode_Dict(dictRes)
        self.stackNode(res)


    def visit_keyword(self, node: ast.keyword) -> Any:
        markerId = self.pushStartMarker()

        keywordParamNode = ASTFuzzerNode_KeywordParam()
        keywordParamNode.paramName = node.arg
        self.visit(node.value)
        keywordParamNode.paramNode = self.popNode()

        self.tryPopMarker(markerId)
        self.stackNode(keywordParamNode)

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
                lastAttrInList : AttributeData = attrNode.listOfAttributesData[-1]
                assert isinstance(lastAttrInList.node, (ASTFuzzerNode_Name, ASTFuzzerNode_Attribute)),\
                    "I was expecting a name for function call !"

                funcCallNode.funcCallName = attrNode.listOfAttributesData[-1].name
                funcCallNode.attributes = attrNode.listOfAttributesData[:-1]
            elif isinstance(topNode, ASTFuzzerNode_Variable):
                nameNode: ASTFuzzerNode_Variable = self.popNode()
                funcCallNode.funcCallName = nameNode.name
                funcCallNode.attributes = []
            else:
                assert False,f"Unkown case {type(topNode)}"
            break

        funcCallNode.args = []

        # Add direct arguments sent
        for funcArg in node.args:
            self.visit(funcArg)
            topNode = self.popNode()
            assert topNode == None or topNode.isMarkerNode() is False, "Invalid expected argument node parsed"
            funcCallNode.args.append(topNode)

        # Add keyword arguments sent e.g. ( args..., row=12, col =123, value=123)
        for funcArgKeyword in node.keywords:
            #raise NotImplementedError("Not needed now and they might even confuse the c# users...")
            self.visit(funcArgKeyword)
            topNode = self.popNode()
            assert isinstance(topNode, ASTFuzzerNode_KeywordParam), "Invalid expected argument node parsed"
            funcCallNode.kwargs[topNode.paramName] = topNode.paramNode

        self.tryPopMarker(markerId)

        self.stackNode(funcCallNode)

    def visit_Num(self, node: ast.Num) -> Any:
        constantNode = None
        if isinstance(node.n, int):
            constantNode = ASTFuzzerNode_ConstantInt(node.n)
        elif isinstance(node.n, (float, c_double, c_longdouble)):
            constantNode = ASTFuzzerNode_ConstantReal(node.n)
        else:
            raise NotImplementedError()

        assert constantNode, "Coudn't fix node"
        self.stackNode(constantNode)

    def visit_NameConstant(self, node: ast.NameConstant) -> Any:
        constantNode = None
        if isinstance(node.value, bool):
            constantNode = ASTFuzzerNode_ConstantBool(node.value)
        else:
            raise NotImplementedError()

        assert constantNode, "Coudn't fix node"
        self.stackNode(constantNode)

    def visit_Name(self, node: ast.Name) -> Any:
        # Special case for true and false => True and False in python.
        if node.id in ["false", "true"]:
            nameVar = ASTFuzzerNode_ConstantBool(node.id)
        else:
            nameVar = ASTFuzzerNode_Variable(node.id)
        self.stackNode(nameVar)

    def visit_Assign(self, node: ast.Assign) -> Any:
        markerId = self.pushStartMarker()

        # Parse the node elements
        self.visit(node.targets[0])
        self.visit(node.value)

        # Now pop the needed element from stack and fill them.
        rightTerm = None

        if isinstance(node.value, (ast.List, ast.Set)):
            rightTerm = []
            for elemValue in node.value.elts:
                rightTerm.append(self.popNode())
            rightTerm.reverse()
        else:
            rightTerm = self.popNode()


        leftTerm = self.popNode()
        self.tryPopMarker(markerId)

        # expected semantic: marker + leftTerm + comparator + rightTerm
        assignNode = ASTFuzzerNode_Assignment()
        assignNode.leftTerm = leftTerm
        assignNode.rightTerm = rightTerm

        # Get back and fill the compare node
        self.stackNode(assignNode)

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        markerId = self.pushStartMarker()

        # Parse the left/right nodes
        self.visit(node.left)
        leftTerm = self.popNode()

        self.visit(node.right)
        rightTerm = self.popNode()

        self.tryPopMarker(markerId)

        mathBinaryNode = ASTFuzzerNode_MathBinary()
        mathBinaryNode.leftTerm = leftTerm
        mathBinaryNode.rightTerm = rightTerm
        mathBinaryNode.op = None

        if isinstance(node.op, ast.Mult):
            mathBinaryNode.op = "*"
        elif isinstance(node.op, ast.Add):
            mathBinaryNode.op = "+"
        elif isinstance(node.op, ast.Sub):
            mathBinaryNode.op = "-"
        elif isinstance(node.op, ast.Div):
            mathBinaryNode.op = "/"
        else:
            raise NotImplementedError()

        assert mathBinaryNode is not None, "Cannot find the math operator for this expression !"

        # Get back and fill the compare node
        self.stackNode(mathBinaryNode)

    def visit_BoolOp(self, node: ast.BoolOp) -> Any:
        markerId = self.pushStartMarker()

        # Parse the left/right nodes
        self.visit(node.values[0])
        leftTerm = self.popNode()

        self.visit(node.values[1])
        rightTerm = self.popNode()

        self.tryPopMarker(markerId)

        logicBinaryNode = ASTFuzzerNode_LogicBinary()
        logicBinaryNode.leftTerm = leftTerm
        logicBinaryNode.rightTerm = rightTerm
        logicBinaryNode.op = None

        if isinstance(node.op, ast.And):
            logicBinaryNode.op = "and"
        elif isinstance(node.op, ast.Or):
            logicBinaryNode.op = "or"
        elif isinstance(node.op, ast.BitXor):
            logicBinaryNode.op = "^"
        else:
            raise NotImplementedError()

        assert logicBinaryNode is not None, "Cannot find the math operator for this expression !"

        # Get back and fill the compare node
        self.stackNode(logicBinaryNode)

    def visit_And(self, node: ast.And) -> Any:
        pass

    # Send a code block expression (possible multiple lines separated by \n, and it will give you back the result
    # in our Fuzzer Nodes AST
    def parseModuleCodeBlock(self, code_block_rawStr : str) -> WorkflowCodeBlockParsed:
        self.reset()

        result: WorkflowCodeBlockParsed = None # result

        # Special expression node for iteration side
        var_pattern_iterObject = '(?P<iteratedObject>(range\([^()]*\))|[a-zA-Z0-9_]+)'
        var_pattern_iterVar = '(?P<iteratorName>[a-zA-Z0-9_]+)'
        match = re.search(f'[\s]*for[\s]+{var_pattern_iterVar}[\s]+in[\s]+{var_pattern_iterObject}', code_block_rawStr)

        if not match: # Regular flow
            # Parse the expr to an AST
            code_block = ast.parse(code_block_rawStr)

            # Then obtain internally the AST with fuzzer nodes
            self.visit(code_block)

            result = self.getFinalOutput()
            assert len(result) == 1, " Currently we expected 1 understandable code block in the input. Do you need more or less ?"
            return result
        else:
            #print(match.group('iteratorName'))
            #if False:
            #    for groupId in match.groups():
            #        print(f"{groupId}")

            iteratedObject_expressionRaw = match.group('iteratedObject')
            iteratedVar_expressionRaw = match.group('iteratorName')

            result : WorkflowCodeBlockParsed = [ASTFuzzerNode_FOREACH()]
            result[0].originalExpression = code_block_rawStr
            result[0].iteratedObject_node = self.parseModuleCodeBlock(iteratedObject_expressionRaw)
            result[0].iteratedVar_node = self.parseModuleCodeBlock(iteratedVar_expressionRaw)
            return result

    # Reset the parser state
    def reset(self):
        self.expectedNumExpressions = None
        self.currentMarkerHead = 0
