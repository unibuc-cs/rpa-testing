# THis is workflow expression parser purpose script, using AST

#================
import sys
import re
from enum import Enum
from typing import Any, List, Dict, Set, Tuple, Union
from Parser_DataTypes import *
from Parser_Functions import *
from SymbolicHelpers import *
from WorkflowGraphBaseNode import *
from Parser_ASTNodes import *

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
            #assert len(result) == 1, " Currently we expected 1 understandable code block in the input. Do you need more or less ?"
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
