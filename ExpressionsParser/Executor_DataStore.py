from typing import Dict
from Parser_WorkflowExpressions import *

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
