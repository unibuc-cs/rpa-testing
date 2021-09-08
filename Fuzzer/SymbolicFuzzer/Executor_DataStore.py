from typing import Dict
from Parser_WorkflowExpressions import *
import random
from Parser_DataTypes import InputSeed

# Data store to handle variables management, either static, dynamic, symbolic, etc
class DataStore:
    def __init__(self):
        self.Values : Dict[str, any] = {}
        self.Types : Dict[str, str] = {}
        self.SymbolicValues : Dict[str, any] = {}
        self.Annotations : Dict[str, any] = {}
        self.DefaultValueExpr : Dict[str, any] = {}

    @staticmethod
    def getIterNameForTheoryArray(nameOfArray):
        return nameOfArray+"_iter"

    # Sets an existing variable value
    def setVariableValue(self, varName, value):
        assert varName in self.Values
        self.Values[varName] = value

    # Gets the default value of a variable.
    # If one was specified in the workflow, that one is used, otherwise we initialize it by default of type (e.g. int is 0 , float is 0.0, False for boolean)
    def getDefaultValueForVar(self, varName : str):
        defaultExpr = self.DefaultValueExpr.get(varName, None)
        defaultValue = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName = self.Types[varName],
                                                                                defaultExpression = self.DefaultValueExpr[varName])
        return defaultValue

    def getRandomValueForVar(self, varName: str):
        assert (varName in self.Types), f"Unknown variable given"
        varTypeName = self.Types[varName]

        # Get the annotation boundaries first if any
        varAnnotation : Tuple[VarAnnotation, None] = None
        if varName in self.Annotations:
            varAnnotation = self.Annotations.get(varName)

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
        elif varTypeName == "Int32[]":
            if varAnnotation.bounds is not None and (varAnnotation.min is not None or varAnnotation.max is not None):
                # Generate a list withing bounds if any specified
                min_boundary = varAnnotation.min if varAnnotation.min is not None else -sys.maxsize
                max_boundary = varAnnotation.max if varAnnotation.max is not None else sys.maxsize
                res = []
                for i in range(int(varAnnotation.bounds)):
                    res.append(random.randint(min_boundary, max_boundary))

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

            # Add the array iterator variable if one was specified
            if varDecl.symbolicGenericIndexVar is not None:
                iterVarName = DataStore.getIterNameForTheoryArray(varDecl.varName)
                self.SymbolicValues[iterVarName] = varDecl.symbolicGenericIndexVar

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

    # Tests if the given variable name is stored behind as a list
    def isVariableOfTypeList(self, varName) -> bool:
        return "[]" in self.Types[varName]

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

    def setInputSeed(self, inputSeed:InputSeed):
        for varName, varValue in inputSeed.content.items():
            contentToSet = inputSeed.content[varName]

            # Check if receiving object is indeed a list / array behind
            if isinstance(self.Values[varName], (FuzzerArray, FuzzerList)):
                assert isinstance(contentToSet, List), "The expected content in this case is a list of items !"
                self.Values[varName].setValAsList(contentToSet)
            # Normal path...if this runs on exception => add a branch for your kind of type too
            # Python doesn't support operator= overload, except for attributes inside the object
            else:
                self.Values[varName] = varValue

    # Gets the SMT conditions based on variables annotations
    def getVariablesSMTConditions(self, forceInputSeed : InputSeed = None) -> List[any]:
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
                # If we have at least one condition for the variables inside arrays
                if (varAnnotation.min != None or varAnnotation.max != None):
                    # If the array is bounded, put the condition on each element
                    if varAnnotation.bounds:
                        for i in range(varAnnotation.bounds):
                            fullIndexVarInContextSpace = f"{varNameInContextSpace}[{i}]"

                            if varAnnotation.min is not None:
                                symbolicExpr = f"{fullIndexVarInContextSpace} >= {varAnnotation.min}"
                                symbolicExpr_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(condToSolve=symbolicExpr,
                                                                                                         contextDataStore=self)

                                res.append(symbolicExpr_inZ3)
                            if varAnnotation.max is not None:
                                symbolicExpr = f"{fullIndexVarInContextSpace} <= {varAnnotation.max}"
                                symbolicExpr_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(condToSolve=symbolicExpr,
                                                                                                         contextDataStore=self)
                                res.append(symbolicExpr_inZ3)

                    # If not, put a generic condition on
                    else:
                        symbolicIteratorName = f"contextDataStore.SymbolicValues[\"{DataStore.getIterNameForTheoryArray(varName)}\"]"
                        self.symbolicExpr = f"ForAll({symbolicIteratorName}, {varNameInContextSpace}[x] >= {varAnnotation.min}, {varNameInContextSpace}[x] <= {varAnnotation.max}))"
                        symbolicExpr_inZ3 = SymbolicExecutionHelpers.convertStringExpressionTOZ3(condToSolve=symbolicExpr,
                                                                             contextDataStore=self)
                        res.append(symbolicExpr_inZ3)

        # TODO Ciprian think about this well
        if forceInputSeed is not None:
            #raise NotImplementedError()
            pass


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
