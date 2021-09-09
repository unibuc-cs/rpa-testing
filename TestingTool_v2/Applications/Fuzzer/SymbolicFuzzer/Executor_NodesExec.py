# THis is the runtime executor
# Many things need to be done at runtime, for example check the SMT stuff in getSymbolicExpressionFromNode func !!!

from Executor_DataStore import *
from Parser_Functions import *
from Parser_DataTypes import *


# An abstract class for references to variables
class VariableRef:
    # parent is a pointer to the variable
    def __init__(self, parentInstace, dataStore : DataStore):
        self.parentInstance = parentInstace
        self.dataStore = dataStore

    def assignValue(self, val):
        pass

    def getValue(self):
        pass

# A reference to a FuzzerArray and a particular index
class FuzzerArrayRefIndex(VariableRef):
    def __init__(self, index, parentInstace: FuzzerArray, dataStore: DataStore):
        super().__init__(parentInstace, dataStore)
        self.index = index

    def assignValue(self, val):
        self.parentInstance.setVal(self.index, val)

    def getValue(self):
        return self.parentInstance.getVal(self.index.val)


# This class will be responsible for the execution of ASTFuzzer nodes
class ASTFuzzerNodeExecutor:
    def __init__(self, DS : DataStore, ExternalCallsDict : DictionaryOfExternalCalls):
        self.DS = DS
        self.ExternalCallsDict = ExternalCallsDict
        ASTFuzzerNode.dataStore = self.DS

    def executeNode(self, node : ASTFuzzerNode):
        if isinstance(node, ASTFuzzerNode_Call):
            args : List[ASTFuzzerNode] = node.args
            kwargs : Dict[str, ASTFuzzerNode] = node.kwargs
            funcName : str = node.funcCallName
            attributes : List[AttributeData] = node.attributes

            # First, arguments list parse and execute
            args_values = [self.executeNode(argNode) for argNode in args]
            kwargs_values = {argName:self.executeNode(argNode) for argName, argNode in kwargs.items()}

            # Then call the functor
            return self._executeNode_FuncCall(funcName=funcName, funcAttrs=attributes, args=args_values, kwargs=kwargs_values)

        elif isinstance(node, ASTFuzzerNode_VariableDecl):
            self.DS.addVariable(node)
            return None

        elif isinstance(node, (list, set)):
            # TODO: should we add a specialized LIST set node for parsing now ?
            fuzzerList = FuzzerList()
            for exprNode in node:
                resExprEval = self.executeNode(exprNode)
                fuzzerList.Add(resExprEval)
            return fuzzerList

        elif isinstance(node, (ASTFuzzerNode_ConstantString, ASTFuzzerNode_ConstantInt, ASTFuzzerNode_ConstantReal, ASTFuzzerNode_ConstantBool)):
            value = node.value
            return value

        elif isinstance(node, ASTFuzzerNode_Subscript):
            # Array is treated using function
            # Currently the use case is when the valueNode[sliceNodes], valueNode is a databale. Will be implemented case by case !
            # Probably list is next !
            valueNodeObj = self.executeNode(node.valueNode)
            sliceNodeObj = self.executeNode(node.sliceNode)

            if isinstance(valueNodeObj, DataTable_iterator):
                return valueNodeObj.getCurrentRowData()[sliceNodeObj]
            elif isinstance(valueNodeObj, DataTable_RowsView):
                return valueNodeObj.Item(sliceNodeObj)
            elif isinstance(valueNodeObj, DataTable_ColumnsView):
                return valueNodeObj.Item(sliceNodeObj)
            elif isinstance(valueNodeObj, DataTable_Row):
                return valueNodeObj.Item(sliceNodeObj)
            elif isinstance(valueNodeObj, DataTable_Column):
                return valueNodeObj.Item(sliceNodeObj)
            else:
                raise NotImplementedError()

            return None
        elif isinstance(node, ASTFuzzerNode_FOREACH):
            # Get special cases of what objects we are iterating on and solve
            if isinstance(node.iteratedObject_node, DataTable):
                # Data table solving
                iteratedObject : DataTable = self.DS.getVariableValue(node.iteratedObject_node.name)

                # Iteration already in progress case
                if iteratedObject.isIterationInProgress():
                    iteratorObj : DataTable_iterator = self.DS.getVariableValue(node.iteratedVar_node.name)
                    assert iteratorObj == iteratedObject.existingIter, "Sanity check failed, not the same object iterating and in progress. Out of sync with DataStore (DS) !"
                    # Move pointer
                    nextRowData = iteratorObj.nextRowIteration()

                    # Is iteration over ?
                    if nextRowData is None:
                        # Close the iterator
                        iteratorObj.closeRowsIteration()

                        # Remove the variable from data store
                        self.DS.removeVariable(node.iteratedVar_node.name)

                        return True
                    else:
                        return False

                else: # New iteration !
                    #Create a new iterator variable and add it to the dictionary
                    dataTableIter = iteratedObject.getIterator()
                    dataTableIter_varDecl = ASTFuzzerNode_VariableDecl(varName=node.iteratedVar_node.name,
                                                                       typeName=DataTable_iterator.__class__.__name__,
                                                                       Default=dataTableIter)
                    self.DS.addVariable(dataTableIter_varDecl)

                    # Now push the node execution again, this time with an in progress iteration to do the checking of the above
                    return self.executeNode(node)

            elif isinstance(node.iteratedObject_node, FuzzerArray):
                # Array object solving
                iteratedObject: DataTable = self.DS.getVariableValue(node.iteratedObject_node.name)

                # Iteration already in progress case
                if iteratedObject.isIterationInProgress():
                    iteratorObj: FuzzerArray_iterator = self.DS.getVariableValue(node.iteratedVar_node.name)
                    assert iteratorObj == iteratedObject.existingIter, "Sanity check failed, not the same object iterating and in progress. Out of sync with DataStore (DS) !"

                    # Move pointer
                    nextData = iteratorObj.nextIteration()

                    # Is iteration over ?
                    if nextData is None:
                        # Close the iterator
                        iteratorObj.closeIteration()

                        # Remove the variable from data store
                        self.DS.removeVariable(node.iteratedVar_node.name)

                        return True
                    else:
                        return False

                else:  # New iteration !
                    # Create a new iterator variable and add it to the dictionary
                    arrayIter = iteratedObject.getIterator()
                    arrayIter_varDecl = ASTFuzzerNode_VariableDecl(varName=node.iteratedVar_node.name,
                                                                       typeName=FuzzerArray_iterator.__class__.__name__,
                                                                       Default=arrayIter)
                    self.DS.addVariable(arrayIter_varDecl)

                    # Now push the node execution again, this time with an in progress iteration to do the checking of the above
                    return self.executeNode(node)

            else:
                raise NotImplementedError()

        elif isinstance(node, AttributeData) and node.subscript != None:
            return self.executeNode(node.subscript)

        elif isinstance(node, ASTFuzzerNode_Dict):
            # execute the nodes inside the dict parsed
            for key,arg in node.value.items():
                node.value[key] = self.executeNode(arg)
            return node.value
        elif isinstance(node, ASTFuzzerNode_Variable):
            # This could be either a real variabile inside dictionary or just a global API name object
            object = self._getObjectInstanceByName(node)
            return object
        elif isinstance(node, ASTFuzzerNode_Attribute):
            object = self._invokeSeriesOfAttributes(node.listOfAttributesData)
            return object

        elif isinstance(node, ASTFuzzerNode_Assignment):
            # Check left and right therms, evaluate them
            leftTerm = node.leftTerm
            rightTerm = node.rightTerm
            assert isinstance(leftTerm, (ASTFuzzerNode_Variable, ASTFuzzerNode_Name))

            leftTermVarName = None
            if isinstance(leftTerm, ASTFuzzerNode_Variable):
                leftTermVarName = leftTerm.name
            elif isinstance(leftTerm, ASTFuzzerNode_Name):
                leftTermVarName = leftTerm.name

            assert leftTermVarName

            rightTermValue = self.executeNode(rightTerm)
            assert rightTermValue != None

            # Then set the new value to the dictionary
            self.DS.setVariableValue(leftTermVarName, rightTermValue)
            return None
        elif isinstance(node, (ASTFuzzerNode_MathBinary, ASTFuzzerNode_LogicBinary)):
            # Check left and right terms, evaluate them
            leftTerm = node.leftTerm
            rightTerm = node.rightTerm

            res_left = self.executeNode(leftTerm)
            res_right = self.executeNode(rightTerm)
            assert res_left != None and res_right != None, "The terms can't be evaluated !"

            if isinstance(node, ASTFuzzerNode_MathBinary):
                if node.op == "*":
                    return res_left * res_right
                elif node.op == "/":
                    assert res_right != 0.0 and res_right != 0
                    return res_left / res_right
                elif node.op == "-":
                    return res_left - res_right
                elif node.op == "+":
                    return res_left + res_right
                else:
                    raise NotImplementedError()
            elif isinstance(node, ASTFuzzerNode_LogicBinary):
                if node.op == "and":
                    return res_left and res_right
                elif node.op == "or":
                    return res_left or res_right
                elif node.op == "^":
                    return res_left ^ res_right
                else:
                    raise NotImplementedError()
            else:
                raise NotImplementedError()
        elif isinstance(node, ASTFuzzerNode_Compare):
            # Check left and right terms, evaluate them
            leftTerm = node.leftTerm
            rightTerm = node.rightTerm

            res_left = self.executeNode(leftTerm)
            res_right = self.executeNode(rightTerm)
            assert res_left and res_right, "The terms can't be evaluated !"

            if node.comparatorClassNode.comparatorClass == ASTFuzzerComparator.COMP_LT:
                return res_left < res_right
            elif node.comparatorClassNode.comparatorClass == ASTFuzzerComparator.COMP_LTE:
                return res_left <= res_right
            elif node.comparatorClassNode.comparatorClass == ASTFuzzerComparator.COMP_GT:
                return res_left > res_right
            elif node.comparatorClassNode.comparatorClass == ASTFuzzerComparator.COMP_GTE:
                return res_left >= res_right
            elif node.comparatorClassNode.comparatorClass == ASTFuzzerComparator.COMP_EQ:
                return res_left == res_right
            elif node.comparatorClassNode.comparatorClass == ASTFuzzerComparator.COMP_NOTEQ:
                return res_left != res_right
            else:
                raise NotImplementedError()
        else:
            raise NotImplementedError("This is not supported yet")

    # Given an AST Fuzzer node as a variabile/name, returns the type begind - a static global object or a dictionary
    # registered variable
    def _getObjectInstanceByName(self, node : ASTFuzzerNode) -> any:
        assert isinstance(node, (ASTFuzzerNode_Variable, ASTFuzzerNode_Name))
        object = None
        if self.DS.hasVariable(node.name):
            object = self.DS.getVariableValue(node.name)
        else:
            object = str2Class(node.name)

        assert object is not None, f"Can't find the object named by {node.name}"
        return object

    def _invokeSeriesOfAttributes(self, listOfAttributes):
        # Get the object behind the first attribute invoked
        firstAttrNode = listOfAttributes[0].node
        if isinstance(listOfAttributes[0], AttributeData) and firstAttrNode is None:
            # In the case of an attribute data note, it could be a subscript beneath !
            firstAttrNode = listOfAttributes[0].subscript

        firstAttrObject = self.executeNode(firstAttrNode)

        # invoke attributes one by one up to the target call function
        currObject = firstAttrObject
        numAttrs = len(listOfAttributes)
        for attrIdx, attData in enumerate(listOfAttributes):
            if attrIdx == 0:
                continue

            assert isinstance(attData, AttributeData)
            # assert currObject.hasattr(attData.name), f"Object {currObject} of type {type(currObject)} doesn't have an attribute named {attData.name} as requested"
            attrToCallOnObject = getattr(currObject, attData.name)
            currObject = attrToCallOnObject()

        return currObject

    def _executeNode_FuncCall(self, funcName : str, funcAttrs : List[AttributeData], args : List[any], kwargs : Dict[any, any]):
        result = None
        # No attribute object, global function call
        if len(funcAttrs) == 0:
            functorToCall = self.ExternalCallsDict.getFunctor(funcName)
            return functorToCall(*args, **kwargs)
        # The case where there are multiple objects invoked before call
        else:
            # Invoke a series of attributes up to the function call
            currObject = self._invokeSeriesOfAttributes(funcAttrs)

            # Now invoke the function
            # We have some custom functions harcoded here because currently we don't plan to support wrapper for
            # Object in C# for exemple. Could be in the future, but doesn't make sense now for performance
            if funcName == "ToString": # add some other Object API functions too if needed
                result = str(currObject)
            elif funcName == "Contains":
                if currObject not in funcAttrs:
                    result = False
                else:
                    result = True
            elif funcName == "Equals":
                if currObject in funcAttrs:
                    result = True
                else:
                    result = False


            else:
                # Retrieve the function attribute and call it
                funcToCallOnObject = getattr(currObject, funcName)
                assert funcToCallOnObject
                result = funcToCallOnObject(*args, **kwargs)

        return result

    # Gets a symbolic expression out of a node
    # WHy this is needed at runtime ?
    # Imagine that we have an expression like this:   if varname < GetThingFromDB("row,col,index") jump X
    # We need to query the DB at runtime !

    # Given a node returns the symbolic expression out of it and a boolean if the expression really contains a symbolic variable
    # (if it doesn't normally it shouldn't be added to the solver !)
    def getSymbolicExpressionFromNode(self, nodeInst : ASTFuzzerNode) -> str:
        if nodeInst.type in [ASTFuzzerNodeType.COMPARE, ASTFuzzerNodeType.MATH_OP_BINARY, ASTFuzzerNodeType.LOGIC_OP_BINARY]:
            # Check if each the two left/right terms. If they contain a symbolic expression we need to get the expr out of it.
            # If not, we just execute the node in the executor and get the result back in plain value !
            leftExpr = None
            isLeftSymbolic = False
            if nodeInst.leftTerm.isAnySymbolicVar():
                leftExpr = self.getSymbolicExpressionFromNode(nodeInst.leftTerm)
                isLeftSymbolic = True
            else:
                leftExpr = self.executeNode(nodeInst.leftTerm)

            rightExpr = None
            isRightSymbolic = False
            if nodeInst.rightTerm.isAnySymbolicVar():
                rightExpr = self.getSymbolicExpressionFromNode(nodeInst.rightTerm)
                isRightSymbolic = True
            else:
                rightExpr = self.executeNode(nodeInst.rightTerm)

            symbolicExprRes = None
            if nodeInst.type == ASTFuzzerNodeType.COMPARE:
                compStr = ASTFuzzerComparatorToStr(nodeInst.comparatorClassNode.comparatorClass)
                symbolicExprRes = f"{leftExpr} {compStr} {rightExpr}"
                return symbolicExprRes

            elif nodeInst.type == nodeInst.type == ASTFuzzerNodeType.LOGIC_OP_BINARY:
                if nodeInst.op == 'and':
                    symbolicExprRes = f"And({leftExpr},{rightExpr})"
                    return symbolicExprRes
                elif nodeInst.op == 'or':
                    symbolicExprRes = f"Or({leftExpr},{rightExpr})"
                    return symbolicExprRes
                elif nodeInst.op == '!=':
                    symbolicExprRes = f"And({leftExpr},{rightExpr})"
                    return symbolicExprRes
            else:
                assert False, "Have to check the correctness of this failure safe branch !" #isinstance(nodeInst.op, str)
                compStr = nodeInst.op
                return None

        elif nodeInst.type in [ASTFuzzerNodeType.VARIABLE, ASTFuzzerNodeType.NAME]: # Get an access to SMT variable in the store
            symbolicExprRes = "self.DS.SymbolicValues["+"\"" + nodeInst.name  + "\"" + "]"
            return symbolicExprRes
        elif nodeInst.type in [ASTFuzzerNodeType.ATTRIBUTE]:
            if nodeInst.subscript is not None:
                return self.getSymbolicExpressionFromNode(nodeInst.subscript)
            else:
                raise NotImplementedError()
        elif nodeInst.type in [ASTFuzzerNodeType.SUBSCRIPT]:
            symbolicFromValue = self.getSymbolicExpressionFromNode(nodeInst.valueNode)
            symbolicFromSlice = self.getSymbolicExpressionFromNode(nodeInst.sliceNode)

            numSymbolicNodes = (1 if symbolicFromSlice is not None else 0) + (1 if symbolicFromValue is not None else 0)
            assert numSymbolicNodes < 2, "Only one of the items should be not none in a symbolic expression, at the moment !"

            if symbolicFromSlice is not None:
                return symbolicFromSlice
            else:
                return symbolicFromValue # Could be also None, no problem.

        elif nodeInst.type == ASTFuzzerNodeType.ASSIGNMENT:
            raise NotImplementedError()
        elif nodeInst.type == ASTFuzzerNodeType.CALL_FUNC:
            # Add here all function calls that are targeted towards symbolic execution
            # Currently we have a single candidate
            symbolicVariableInvoked = self.DS.getSymbolicVariableValue(nodeInst.attributes[-1].name)
            if symbolicVariableInvoked and (nodeInst.funcCallName in ["GetElementAt"]):
                # Get the slice index
                assert len(nodeInst.args) == 1, "Where is the index parameter ?"
                arg_sliceValue = self.executeNode(nodeInst.args[0])
                expr_res = "self.DS.SymbolicValues[" + "\"" + nodeInst.attributes[-1].name + "\"" + "][" + str(arg_sliceValue) +"]"
                return expr_res

            return None
        else:
            return None



