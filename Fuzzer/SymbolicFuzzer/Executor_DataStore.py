from typing import Dict
from Parser_WorkflowExpressions import *
import random
from Parser_DataTypes import ConcolicInputSeed

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

    # Gets the default value of a variable.
    # If one was specified in the workflow, that one is used, otherwise we initialize it by default of type (e.g. int is 0 , float is 0.0, False for boolean)
    def getDefaultValueForVar(self, varName : str):
        defaultExpr = self.DefaultValueExpr.get(varName, None)
        defaultValue = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName = self.Types[varName],  defaultExpression = self.DefaultValueExpr[varName])
        return defaultValue

    def getRandomValueForVar(self, varName: str):
        assert (varName in self.Types), f"Unknown variable given"
        varTypeName = self.Types[varName]

        # Get the annotation boundaries first if any
        varAnnotation : Tuple[VarAnnotation, None] = None
        if varName in self.dataStoreTemplate.Annotations:
            varAnnotation = self.dataStoreTemplate.Annotations.get(varName)

        res = None
        if varTypeName == "Int32":
            if varAnnotation:
                # Generate a random value according to ranges put
                if varAnnotation.min is not None and varAnnotation.max is not None:
                    res = random.randint(int(varAnnotation.min), int(varAnnotation.max))
                elif varAnnotation.min is not None:
                    res = random.randint(int(varAnnotation.min), sys.maxsize)
                elif varAnnotation.max is not None:
                    res = random.randint(-sys.maxsize, int(varAnnotation.max))
            elif varTypeName == 'Boolean':
                # You can either put a default value or nothing here...
                res = False
            else:
                raise NotImplementedError("Do it yourself !!")

        return res

    def resetToDefaultValues(self):
        for varName in self.DefaultValueExpr:
            self.Values[varName] = self.getDefaultValueForVar(varName)

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

    def getUserInputVariables(self) -> List[str]:
        res : List[str] = []
        for varName, varAnnotation in self.Annotations.items():
            if varAnnotation.isFromUserInput:
                res.append(varName)
        return res

    # Gets the SMT conditions based on variables annotations
    def getVariablesSMTConditions(self, forceInputSeed : ConcolicInputSeed = None) -> List[any]:
        res : List[any] = []

        # Iterate over all symbolic values and take each one annotation conditions
        for varName, varZ3Ref in self.SymbolicValues.items():
            if varZ3Ref == None:
                continue

            varType : str = self.Types[varName]
            varAnnotation : VarAnnotation = self.Annotations[varName]

            # Why do we put contextDataStore.SymbolicValues ? this will be called later when evaluating the conditions using z3.eval
            # It needs to know where to take the values from and this is the parameter link if you follow the code (func call)
            varNameInContextSpace = f"contextDataStore.SymbolicValues[\"{varName}\"]"

            if varType == "Int32" or varType == "Int" or varType == "Float":
                if varAnnotation.min is not None:
                    symbolicExpr = f"{varNameInContextSpace} >= {varAnnotation.min}"
                    symbolicExpr_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(
                                                            condToSolve=symbolicExpr,
                                                            contextDataStore=self)
                    res.append(symbolicExpr_inZ3)
                if varAnnotation.max is not None:
                    symbolicExpr = f"{varNameInContextSpace} <= {varAnnotation.max}"
                    symbolicExpr_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(
                        condToSolve=symbolicExpr,
                        contextDataStore=self)
                    res.append(symbolicExpr_inZ3)
            elif varType == "Int32[]" or varType == "Int[]" or varType == "Float[]":
                pass

        if forceInputSeed is not None:
            raise NotImplementedError()

        return res


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
