
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
    ASSIGNMENT = 16

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

#  Base class for all nodes
class ASTFuzzerNode:
    def __init__(self, type : ASTFuzzerNodeType):
        self.type : ASTFuzzerNodeType = type

    def isMarkerNode(self) -> bool:
        return self.type == ASTFuzzerNodeType.MARKER

# Attribute data. currently a pair of node and string to processes easier in some cases
class AttributeData:
    def __init__(self, node : ASTFuzzerNode, name : str):
        self.node = node
        self.name = name

class ASTFuzzerNode_VariableDecl(ASTFuzzerNode):
    """ E.g.
    "local_number_retries": {
        "Type": "Int32",
        "Default": "0"
    },
    """
    # Will put the variabile in the datastore
    def __init__(self, varName : str, typeName : str, **kwargs):
        super().__init__(ASTFuzzerNodeType.VARIABLE_DECL)
        self.typeName = typeName
        self.value = kwargs['defaultVal'] if 'defaultVal' in kwargs else None
        self.varName = varName

        if typeName == "Int32":
            self.value = int(self.value)
        elif typeName == 'Boolean':
            self.value = False if (self.value == 'false' or self.value == 'False' or int(self.value) == 0) else True
        elif typeName == "DataTable":
            lazyLoad = True if 'lazyLoad' not in kwargs else kwargs['lazyLoad']
            path = None if 'path' not in kwargs else kwargs['path']
            self.value = DataTable(path=path, lazyLoad=lazyLoad)
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
        self.listOfAttributesData : List[AttributeData] = [] # A list of attribute names expected ???

    def addOther(self, other):
        if isinstance(other, ASTFuzzerNode_Attribute):
            self.listOfAttributesData.extend(other.listOfAttributesData)
        elif isinstance(other, ASTFuzzerNode_Name):
            self.listOfAttributesData.append(AttributeData(node=other, name=other.name))
        elif isinstance(other, ASTFuzzerNode_Variable):
            self.listOfAttributesData.append(AttributeData(node=other, name=other.variableName))
        elif isinstance(other, ASTFuzzerNode_Call):
            self.listOfAttributesData.append(AttributeData(node=other, name=other.funcCallName))
        else:
            assert False

class ASTFuzzerNode_Assignment(ASTFuzzerNode):
    def __init__(self):
        super().__init__(ASTFuzzerNodeType.ASSIGNMENT)
        self.leftTerm: ASTFuzzerNode = None
        self.rightTerm: ASTFuzzerNode = None

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

        self.attributes : List[AttributeData] # The list of attributes used before call name
        self.funcCallName : str # the function being invoked by the list of attributes above
        self.args : List[ASTFuzzerNode] = [] # The argument nodes

class ASTForFuzzer:
    def __init__(self):
        self.dictOfExternalCalls : DictionaryOfExternalCalls = {}

WorkflowCodeBlockParsed = List[ASTFuzzerNode]

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
            assert isinstance(exprNode, ast.Expr) or isinstance(exprNode, ast.Assign)
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

    def visit_keyword(self, node: ast.keyword) -> Any:
        raise NotImplementedError

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
                assert isinstance(lastAttrInList.node, ASTFuzzerNode_Name)\
                    or isinstance(lastAttrInList.node, ASTFuzzerNode_Attribute), "I was expecting a name for function call !"

                funcCallNode.funcCallName = attrNode.listOfAttributesData[-1].name
                funcCallNode.attributes = attrNode.listOfAttributesData[:-1]
            elif isinstance(topNode, ASTFuzzerNode_Variable):
                nameNode: ASTFuzzerNode_Variable = self.popNode()
                funcCallNode.funcCallName = nameNode.variableName
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
            raise NotImplementedError("Not needed now and they might even confuse the c# users...")
            self.visit(funcArgKeyword)
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
        markerId = self.pushStartMarker()

        # Parse the node elements
        self.visit(node.targets[0])
        self.visit(node.value)

        # Now pop the needed element from stack and fill them.
        rightTerm = self.popNode()
        leftTerm = self.popNode()
        self.tryPopMarker(markerId)

        # expected semantic: marker + leftTerm + comparator + rightTerm
        assignNode = ASTFuzzerNode_Assignment()
        assignNode.leftTerm = leftTerm
        assignNode.rightTerm = rightTerm

        # Get back and fill the compare node
        self.stackNode(assignNode)

    def visit_And(self, node: ast.And) -> Any:
        pass


    # Send a code block expression (possible multiple lines separated by \n, and it will give you back the result
    # in our Fuzzer Nodes AST
    def parseModuleCodeBlock(self, code_block_ast) -> WorkflowCodeBlockParsed:
        self.reset()

        # Parse the expr to an AST
        code_block = ast.parse(code_block_ast)

        # Then obtain internally the AST with fuzzer nodes
        self.visit(code_block)

        result: WorkflowCodeBlockParsed = self.getFinalOutput()

        return result

    # Reset the parser state
    def reset(self):
        self.expectedNumExpressions = None
        self.currentMarkerHead = 0



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

    def getVariableType(self, varName)-> str:
        return self.Types[varName]

    def hasVariable(self, varName) -> bool:
        return varName in self.Values

# This class will be responsible for the execution of ASTFuzzer nodes
class ASTFuzzerNodeExecutor:
    def __init__(self, DS : DataStore, ExternalCallsDict : DictionaryOfExternalCalls):
        self.DS = DS
        self.ExternalCallsDict = ExternalCallsDict

    def executeNode(self, node : ASTFuzzerNode):
        if isinstance(node, ASTFuzzerNode_Call):
            args : List[ASTFuzzerNode] = node.args
            funcName : str = node.funcCallName
            attributes : List[AttributeData] = node.attributes

            # First, arguments list parse and execute
            args_values = [self.executeNode(argNode) for argNode in args]

            # Then call the functor
            return self._executeNode_FuncCall(funcName=funcName, funcAttrs=attributes, args=args_values)

        elif isinstance(node, ASTFuzzerNode_VariableDecl):
            self.DS.addVariable(node)
            return None
        elif isinstance(node, list):
            for exprNode in node:
                self.executeNode(exprNode)

        elif isinstance(node, (ASTFuzzerNode_ConstantString, ASTFuzzerNode_ConstantInt, ASTFuzzerNode_ConstantReal)):
            value = node.value
            return value
        elif isinstance(node, ASTFuzzerNode_Variable) or isinstance(node, ASTFuzzerNode_Attribute):
            # This could be either a real variabile inside dictionary or just a global API name object
            object = self._getObjectInstanceByName(node)
            return object
        elif isinstance(node, ASTFuzzerNode_Assignment):
            # Check left and right therms, evaluate them
            leftTerm = node.leftTerm
            rightTerm = node.rightTerm
            assert isinstance(leftTerm, (ASTFuzzerNode_Variable, ASTFuzzerNode_Name))

            leftTermVarName = None
            if isinstance(leftTerm, ASTFuzzerNode_Variable):
                leftTermVarName = leftTerm.variableName
            elif isinstance(leftTerm, ASTFuzzerNode_Name):
                leftTermVarName = leftTerm.name

            assert leftTermVarName

            rightTermValue = self.executeNode(rightTerm)
            assert rightTermValue

            # Then set the new value to the dictionary
            self.DS.setVariableValue(leftTermVarName, rightTermValue)
            return None
        else:
            raise NotImplementedError("This is not supported yet")

    # Given an AST Fuzzer node as a variabile/name, returns the type begind - a static global object or a dictionary
    # registered variable
    def _getObjectInstanceByName(self, node : ASTFuzzerNode) -> any:
        assert isinstance(node, (ASTFuzzerNode_Variable, ASTFuzzerNode_Name))
        object = None
        if self.DS.hasVariable(node.variableName):
            object = self.DS.getVariableValue(node.variableName)
        else:
            object = str2Class(node.variableName)

        assert object is not None, f"Can't find the object named by {node.variableName}"
        return object

    def _executeNode_FuncCall(self, funcName : str, funcAttrs : List[AttributeData], args : List[any]):
        result = None
        # No attribute object, global function call
        if len(funcAttrs) == 0:
            functorToCall = self.ExternalCallsDict.getFunctor(funcName)
            return functorToCall(*args)
        # The case where there are multiple objects invoked before call
        else:
            # Get the object behind the first attribute invoked
            firstAttrObject = self.executeNode(funcAttrs[0].node)

            # invoke attributes one by one up to the target call function
            currObject = firstAttrObject
            numAttrs = len(funcAttrs)
            for attrIdx, attData in enumerate(funcAttrs):
                if attrIdx == 0:
                    continue

                assert isinstance(attData, AttributeData)
                #assert currObject.hasattr(attData.name), f"Object {currObject} of type {type(currObject)} doesn't have an attribute named {attData.name} as requested"
                attrToCallOnObject = getattr(currObject, attData.name)
                currObject = attrToCallOnObject()

            # Now invoke the function
            # We have some custom functions harcoded here because currently we don't plan to support wrapper for
            # Object in C# for exemple. Could be in the future, but doesn't make sense now for performance
            if funcName == "ToString": # add some other Object API functions too if needed
                result = str(currObject)
            else:
                # Retrieve the function attribute and call it
                funcToCallOnObject = getattr(currObject, funcName)
                assert funcToCallOnObject
                result = funcToCallOnObject(*args)

        return result

def unitTest1():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = MainWorkflowParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl("myStr",
                                          'Int32',
                                          defaultVal=123)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Call a simple print function registered externally
    code_block = "PrettyPrint(\"the value of variable is \", myStr)"
    result : WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    return

def unitTest2():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = MainWorkflowParser()

    ourMainWorkflowParser.reset()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl("myStr", 'Int32', defaultVal=123)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Test code: Convert it to string, then to integer, then to float
    code_block = "PrettyPrint(Float.Parse(Int32.Parse(myStr.ToString())))"
    #code_block = "PrettyPrint(myStr.ToString())"
    code_block = ast.parse(code_block)

    ourMainWorkflowParser.visit(code_block)
    result: List[ASTFuzzerNode] = ourMainWorkflowParser.getFinalOutput()

    res = astFuzzerNodeExecutor.executeNode(result)

    pass

def unitTest3():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = MainWorkflowParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="local_test_data", typeName='DataTable', lazyLoad=False, path="pin_mocked_data.csv")
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Call a simple print function registered externally
    code_block = "PrettyPrint(Int32.Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString()))"
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    return

def unitTest4():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = MainWorkflowParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="local_test_data", typeName='DataTable', lazyLoad=True)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Call a simple print function registered externally
    code_block = "local_test_data = LoadCSV(\"pin_mocked_data.csv\")"
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    return

def unitTest5():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = MainWorkflowParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="local_test_data", typeName='DataTable', lazyLoad=True)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    code_block = r'''
local_test_data = LoadCSV("pin_mocked_data.csv")
PrettyPrint(Int32.Parse(local_test_data.Rows.Item(0).Item("Pin:expected_pin").ToString()))
PrettyPrint("Max col: ", local_test_data.Max("Pin:expected_pin"))
PrettyPrint("Min col: ", local_test_data.Min("Pin:expected_pin"))
PrettyPrint("Sum col: ", local_test_data.Sum("Pin:expected_pin"))
local_test_data.UpdateValue(1, "Pin:expected_pin", 9999)
PrettyPrint("Max col after new add: ", local_test_data.Max("Pin:expected_pin"))
local_test_data.SaveToCSV("pin_mocked_data_new.csv")
    '''

    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)



    code = r'''
    print('\n')
    print('hello world')
    '''
    """
    # Call a simple print function registered externally
    code_block = r"local_test_data = LoadCSV(\"pin_mocked_data.csv\")"
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    code_block = 'PrettyPrint("Max col: local_test_data.Max(\"Pin:expected_pin\"))'
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    code_block = 'PrettyPrint(local_test_data.Min(\"Pin:expected_pin\"))'
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    code_block = 'PrettyPrint(local_test_data.Sum(\"Pin:expected_pin\"))'
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)
    """

if __name__ == '__main__':
    #unitTest1()
    #unitTest2()
    #unitTest3()
    unitTest4()
    unitTest5()

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
