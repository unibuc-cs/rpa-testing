from typing import Dict
from Parser_WorkflowExpressions import *

# Data store to handle variables management, either static, dynamic, symbolic, etc
class DataStore:
    def __init__(self):
        self.Values : Dict[str, any] = {}
        self.Types : Dict[str, str] = {}
        self.SymbolicValues : Dict[str, any] = {}
        self.Annotations : Dict[str, any] = {}
        self.DefaultValueExpr : Dict[str, any] = {}

    # Sets an existing variable value
    def setVariableValue(self, varName, value):
        assert varName in self.Values
        self.Values[varName] = value


    def resetToDefaultValues(self):
        for varName in self.DefaultValueExpr:
            defaultExpr = self.DefaultValueExpr[varName]
            if defaultExpr is None or defaultExpr == "":
                continue

            self.Values[varName] = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName=self.Types[varName],
                                                                                            defaultExpression=self.DefaultValueExpr[varName])

    # ADds a variabile
    def addVariable(self, varDecl : ASTFuzzerNode_VariableDecl):
        assert varDecl.varName not in self.Values and varDecl.varName not in self.Types
        self.Values[varDecl.varName] = varDecl.value
        self.Types[varDecl.varName] = varDecl.typeName

        if varDecl.annotation and varDecl.annotation.isFromUserInput:
            self.SymbolicValues[varDecl.varName] = varDecl.symbolicValue

        self.Annotations[varDecl.varName] = varDecl.annotation
        self.DefaultValueExpr[varDecl.varName] = varDecl.defaultValue

    def removeVariable(self, varName):
        self.Values.pop(varName)
        self.Types.pop(varName)
        self.SymbolicValues.pop(varName)
        self.Annotations.pop(varName)

    # Retrieve the value of a variable
    def getVariableValue(self, varName) -> any:
        return self.Values[varName]

    def getSymbolicVariableValue(self, varName) -> any:
        return self.SymbolicValues.get(varName)

    def getVariableType(self, varName)-> str:
        return self.Types[varName]

    def hasVariable(self, varName) -> bool:
        return varName in self.Values

    def isVariableSymbolic(self, varName) -> bool:
        res = self.getSymbolicVariableValue(varName)
        return res is not None

    def __copy__(self):
        # For now, just create a new type and move dictionaries...
        newObj = type(self)()
        newObj.__dict__.update(self.__dict__)
        return newObj

    def __deepcopy__(self, memodict={}):
        # For now, we keep the symbolic variables, but clone the concrete values
        newObj = type(self)()
        newObj.__dict__.update(self.__dict__)
        newObj.Values = copy.deepcopy(self.Values)
        return newObj
