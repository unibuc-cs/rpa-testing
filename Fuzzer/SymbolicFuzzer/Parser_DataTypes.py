# MOCKING DataTypes !
# The purpose of this file is to offer a default implementation of data types.
# The user can then import a file or dictionary, or inject through the sys modules API new Data Types !
# By default we support a few DataTypes very common in C# and a kind of DataTables to create mockups for databases through csv files

""" Notes:
If you define a class like:

class MyClass
  def func1(self , params...)
    ...

  # or static ones:
  @staticmethod
  def funcStatic1(params....)
    ....

then you can invoke from the Annotation code:

# Step 0: declare a variabile like this:
myVar = MyClass()

# Step 1: use the functions above
myVar.func1() or
myVar.func2()

Check the more complex examples below and in your manual
"""
import copy
import os
import sys
import pandas as pd
from typing import Dict
import ast

# Configuration debugging
class DebuggingOptions():
    def __init__(self):
        self.debug_outputGraphFile : str = None
        self.debug_consoleOutput = False
        self.debug_tests_fullPaths = False
        self.debug_tests_fullVariablesContent = False

    # Parse from arguments func
    def parseFromArgs(self, args):
        outputGraphFilePath = args.debug_outputGraphFile.strip()
        self.debug_outputGraphFile = outputGraphFilePath if len(outputGraphFilePath) > 0 else None
        self.debug_consoleOutput = args.debug_consoleOutput == 1
        self.debug_tests_fullPaths = args.debug_tests_fullPaths == 1
        self.debug_tests_fullVariablesContent = args.debug_tests_fullVariablesContent == 1

# Each entry is a dict from variable name to its value
class InputSeed():
    DEFAULT_PRIORITY = 0    # Default and highest priority
    def __init__(self):
        self.content : Dict[str, any] = {}
        self.priority : int = 0
        self.concolicBoundaryIndex : int = 0

def removeNamespacesFromName(nameToParse):
    splitByNamespaces = nameToParse.split(":")
    assert len(splitByNamespaces) > 0
    return splitByNamespaces[-1]

# From str to API object
def str2Class(str):
    if hasattr(sys.modules[__name__], str):
        return getattr(sys.modules[__name__], str)
    else:
        strWithoutNamespaces = removeNamespacesFromName(str)
        if hasattr(sys.modules[__name__], strWithoutNamespaces): # Failsafe without namespace ?
            return getattr(sys.modules[__name__], strWithoutNamespaces)
        else:
            return None
    return None

# Given the type of the variable as a string and the expression containing the default value, get the default object value
def getDefaultValueFromExpression(varTypeName: str, defaultExpression: str) -> any:
    res = None
    if varTypeName == "Int32":
        res = 0 if defaultExpression is None else int(defaultExpression)
    elif varTypeName == 'Boolean':
        res = False if (defaultExpression == None or defaultExpression == 'false' or defaultExpression == 'False'
              or int(defaultExpression) == 0) else True
    elif varTypeName == "Int32[]":
        res = [] if defaultExpression is None else ast.literal_eval(defaultExpression)
        assert isinstance(res, list), " The element given as default in this case must be a list !!!"
    elif varTypeName == "String":
        res = "" if defaultExpression is None else ast.literal_eval(defaultExpression)
    else:
        raise NotImplementedError("Do it yourself !!")

    return res

# An Object kind of thing that has a value and can be converted to values
# Purpose to call obj.ToString() and some others

class VarAnnotation:
    def __init__(self):
        # This is to mark if the variabile comes from an user input or not
        self.isFromUserInput = False
        self.min = None
        self.max = None
        self.bounds = None
        self.defaultValue = None

class ObjectValue:
    def __init__(self, value):
        self.value = value

    def ToString(self):
        return str(self.value)

# Int32 mock
class Int32:
    def __init__(self):
        pass

    @staticmethod
    def Parse(value):
        try:
            valueAsInt = int(value)
            return valueAsInt
        except:
            print(f"can't convert value {value} of type {type(value)} to Int")

# Float mock
class Float:
    def __init__(self):
        pass

    @staticmethod
    def Parse(value):
        try:
            valueAsFloat = float(value)
            return valueAsFloat
        except:
            print(f"can't convert value {value} of type {type(value)} to Int")


######### # Data tables default logic
class DataTable_Column:
    def __init__(self, data):
        self.data : pd.DataFrame = data

    def Item(self, row):
        if isinstance(row, int):
            return self.data[row]
        elif isinstance(row, str):
            return self.data[row]
        else:
            raise NotImplementedError("Not supported")

    def __call__(self):
        return self

# Data table row access
class DataTable_Row:
    def __init__(self, data):
        self.data : pd.Series = data

    def Item(self, column):
        if isinstance(column, int):
            return self.data[column]
        elif isinstance(column, str):
            return self.data[column]
        else:
            raise NotImplementedError("Not supported")

    def __call__(self):
        return self

class DataTable_RowsView:
    def __init__(self, data):
        self.data : pd.DataFrame = data

    def Item(self, index) -> DataTable_Row:
        return DataTable_Row(self.data.iloc[index])

    def NumItems(self) -> int:
        return self.data.shape[0]

    def Count(self) -> int:
        return self.NumItems()

    def __call__(self):
        return self

class DataTable_ColumnsView:
    def __init__(self, data):
        self.data : pd.DataFrame = data

    def Item(self, index) -> DataTable_Column:
        return DataTable_Column(self.data[index])

    def __call__(self):
        return self

class DataTable_iterator:
    def __init__(self, parentTable):
        self.parentTable = parentTable

        self.rowsView  : DataTable_RowsView = None
        self.rowIterIndex = None
        self.expectedNumRows = None

    # ITERATION LOGIC
    #-------------------------------------
    # Checks if we are already iterating over the database or not
    # If not, we start it, if yes do nothing
    def checkStartRowIteration(self) -> bool:
        if self.rowsView is None:
            self.rowsView = self.parentTable.Rows
            self.expectedNumRows = self.rowsView.data.items()
            self.rowIterIndex = -1
            return True
        else:
            return False

    def nextRowIteration(self):
        assert(self.rowsView is not None)
        self.rowIterIndex += 1

        # Check if it should close
        if self.rowIterIndex == self.expectedNumRows:
            self.closeRowsIteration()
            return None

        return self.rowsView.data[self.rowIterIndex]

    def getCurrentRowData(self):
        if self.rowsView is None:
            return None
        return self.rowsView.data[self.rowIterIndex]

    def closeRowsIteration(self):
        self.rowsView = None
        self.expectedNumRows = None
        self.rowIterIndex = None
        self.parentTable.clearIterator()
    # --- END ITERATION LOGIC -------------------------------------

class DataTable:
    def __init__(self, **kwargs):
        self.path = kwargs["path"]
        self.data = None
        self.lazyLoad = kwargs["lazyLoad"]
        self.existingIter : DataTable_iterator = None
        if not self.lazyLoad:
            self.__load()

    def __call__(self):
        return self

    # This should be called when using the lazy load to check data is loaded or not
    def _checkInit(self):
        if self.data is None:
            self.__load()

    @property
    def Rows(self):
        self._checkInit()
        return DataTable_RowsView(self.data)

    @property
    def DataRow(self):
        return self.Rows()

    @property
    def Columns(self):
        self._checkInit()
        return DataTable_ColumnsView(self.data)

    @property
    def DataColumn(self):
        return self.Columns()

    # Some aggregate functions for columns
    def Max(self, column):
        colValues = self.data[column]
        res = colValues.max()
        return res
    def Min(self, column):
        colValues = self.data[column]
        res = colValues.min()
        return res

    def Sum(self, column):
        colValues = self.data[column]
        res = colValues.sum()
        return res

    # Set a given value on a row and column
    def UpdateValue(self, row, column, value):
        self.data.iloc[row][column] = value
        return True

    # Set a given value on a row and column
    def AppendRow(self, data):
        self.data.loc[len(self.data.index)] = data
        return True

    # Saves the current datatable to a file (could be the same or other)
    def SaveToCSV(self, filePath : str):
        self.data.to_csv(path_or_buf=filePath, index=False)

    def __load(self):
        # TODO
        self.data = pd.read_csv(self.path)

    # Creates a persistent iterator on
    def getIterator(self) -> DataTable_iterator:
        assert self.existingIter is None
        newIter = DataTable_iterator(self)
        self.existingIter = newIter
        return newIter

    # Returns true if there is an iteration in progress
    def isIterationInProgress(self) -> bool:
        return self.existingIter is not None

    def clearIterator(self):
        assert self.existingIter is not None
        self.existingIter = None

    def __str__(self):
        if self.data is None:
            return ""

        #return self.data.to_string()
        return str(self.data.values.tolist())

class FuzzerArray_iterator:
    def __init__(self, parentArray):
        self.parentArray = parentArray
        self.currentIndex = None
        self.expectedNumItems = None

    # ITERATION LOGIC
    #-------------------------------------
    # Checks if we are already iterating over the array or not
    # If not, we start it, if yes do nothing
    def checkStartIteration(self) -> bool:
        if self.currentIndex is None:
            self.expectedNumItems = len(self.parentArray.internalValue)
            self.currentIndex = -1
            return True
        else:
            return False

    def nextIteration(self):
        assert(self.currentIndex is not None)
        self.currentIndex += 1

        # Check if it should close
        if self.currentIndex == self.expectedNumItems:
            self.closeIteration()
            return None

        return self.parentArray.internalValue[self.currentIndex]

    def getCurrentData(self):
        if self.currentIndex is None:
            return None
        return self.parentArray.internalValue[self.currentIndex]

    def closeIteration(self):
        self.rowsView = None
        self.expectedNumRows = None
        self.rowIterIndex = None
        self.parentTable.clearIterator()
    # --- END ITERATION LOGIC -------------------------------------

class FuzzerArray:
    def __init__(self, internalDataType : str, annotation : VarAnnotation, defaultValue = None):
        self.internalDataType = internalDataType
        self.annotation = annotation
        self.defaultValue = defaultValue
        self.internalValue = None
        self.existingIter = None

        if self.annotation.isFromUserInput:
            self.internalValue = [] #SymbolicHelpers.createVariable()
        else:
            self.internalValue = [] if self.annotation.bounds is None else [self.defaultValue]*self.annotation.bounds

    # Retrieve the element from a particular index by creating a fuzzer array index ref
    # This actually mimics the C# code
    def elementAt(self, index): #->FuzzerArrayRefIndex:
        res = FuzzerArrayRefIndex(index)
        return res

    # A static helper to create an array given a type, annotation and a default value
    @staticmethod
    def CreateArray(internalType : str, annotation : VarAnnotation = None, defaultValue = None):
        res = FuzzerArray(internalType, annotation, defaultValue)
        return res

    # set/get value at an index, creates no references as elementAt does
    def SetElementAt(self, index, val):
        self.setVal(index, val)

    def GetElementAt(self, index):
        return self.getVal(index)

    def setVal(self, index, val):
        self.internalValue[index] = val

    def setValAsList(self, listVal):
        # Get the bounds of the array
        internalValueLength = int(self.annotation.bounds) if self.annotation.bounds is not None else 0
        internalValueLength = max(internalValueLength, len(listVal))

        # Get the default value by internal type and allocate an initial data vector with that value.
        defaultValuePerType = getDefaultValueFromExpression(self.internalDataType, defaultExpression=None)
        self.internalValue = [defaultValuePerType]*internalValueLength

        # Now get all the values in the given list and fill the internal value
        for itemIndex, itemValue in enumerate(listVal):
            self.internalValue[itemIndex] = itemValue

    def getVal(self, index):
        return self.internalValue[index]

    # Returns a list with all content stored
    def getAllContent(self):
        return self.internalValue

    # Creates a persistent iterator on
    def getIterator(self) -> FuzzerArray_iterator:
        assert self.existingIter is None
        newIter = FuzzerArray_iterator(self)
        self.existingIter = newIter
        return newIter

    # Returns true if there is an iteration in progress
    def isIterationInProgress(self) -> bool:
        return self.existingIter is not None

    def clearIterator(self):
        assert self.existingIter is not None
        self.existingIter = None

    def __str__(self):
        if self.internalValue is None:
            return ""
        return str(self.internalValue)

class FuzzerList:
    def __init__(self, annotation : VarAnnotation, defaultValue = None):
        self.annotation = annotation
        self.defaultValue = defaultValue
        self.internalValue = None
        self.existingIter = None

        self.internalValue = self.defaultValue if self.defaultValue is not None else []

    # A static helper to create an array given a type, annotation and a default value
    @staticmethod
    def Create(annotation : VarAnnotation = None, defaultValue = None):
        res = FuzzerList(annotation, defaultValue)
        return res

    # set/get value at an index, creates no references as elementAt does
    def SetElementAt(self, index, val):
        self.setVal(index, val)

    def GetElementAt(self, index):
        return self.getVal(index)

    def setVal(self, index, val):
        self.internalValue[index] = val

    def setValAsList(self, listVal):
        self.internalValue = copy.deepcopy(listVal)

    def getVal(self, index):
        return self.internalValue[index]

    # Returns a list with all content stored
    def getAllContent(self):
        return self.internalValue

    # Creates a persistent iterator on
    def getIterator(self) -> FuzzerArray_iterator:
        assert self.existingIter is None
        newIter = FuzzerArray_iterator(self)
        self.existingIter = newIter
        return newIter

    # Returns true if there is an iteration in progress
    def isIterationInProgress(self) -> bool:
        return self.existingIter is not None

    def clearIterator(self):
        assert self.existingIter is not None
        self.existingIter = None

    def Add(self, item):
        self.internalValue.append(item)

    def __str__(self):
        if self.internalValue is None:
            return ""
        return str(self.internalValue)



# Main idea is to offer a high level management of dictionaries.
# In the background, if the name of dictionary is DNAME, then each key will be named DNAME_KEY and stored in the DataStore.
# The backend , i.e., this class, will hide this.
class DictionaryWithStringKey:
    def __init__(self, thisDictionaryName: str, valueDataType: str, valuesAnnotation: VarAnnotation, parentDataStore):
        assert valuesAnnotation.bounds is None, "Dictionaries shouldn't have bounds set. Leave it as many as possible items"
        self.valueDataType = valueDataType
        self.valuesAnnotation = valuesAnnotation
        #self.internalValue = None
        self.existingIter = None
        self.parentDataStore = parentDataStore
        self.thisDictionaryName = thisDictionaryName

        self.allKeysStored = set()

        """
        if self.valuesAnnotation.isFromUserInput:
            self.internalValue = {}  # SymbolicHelpers.createVariable()
        else:
            self.internalValue = {}
        """

    # Retrieve the element for a particular key as a reference so further code can modify it directly
    # This actually mimics the C# code somehow
    def get(self, key : str):
        assert key in self.internalValue, f"the value for a key named {key} was not set yet in the dictonary!"
        res = DictionaryKeyValueRef(key)
        return res

    # A static helper to create an array given a type, annotation and a default value
    @staticmethod
    def Create(thisDictionaryName : str, valueDataType: str, valuesAnnotation: VarAnnotation = None, parentDataStore= None):
        res = DictionaryWithStringKey(thisDictionaryName, valueDataType, valuesAnnotation, parentDataStore = parentDataStore)
        return res

    def __getfullVariableNameByKey(self, key:str):
        fullVariableKeyName = self.thisDictionaryName+"_"+key
        return fullVariableKeyName

    # Sets a value, both symbolically and concrete
    def setVal(self, key: str, val):
        fullVariableKeyName = self.__getfullVariableNameByKey()

        # Remove the variable if already in there
        if self.parentDataStore.hasVariable(fullVariableKeyName):
            self.__removeVal_internal(fullVariableKeyName)

        # Declare the new variable and add it to the data store by executing the context
        # Note that we pass in the value through the default Value, in current use cases we don't need more.
        # If needed, we can an assignment node and execute it
        varDecl = ASTFuzzerNode_VariableDecl(varName=fullVariableKeyName, typeName=self.valueDataType,
                                             defaultValue=val, annotation=self.valuesAnnotation,
                                             currentContextDataStore = self.parentDataStore)    # ADds a variabile

        currentASTFuzzerNodeExecutor = globals()['currentASTFuzzerNodeExecutor']
        assert currentASTFuzzerNodeExecutor, "at this point i was expecing this to be set !!!. No constructor was called for it"
        currentASTFuzzerNodeExecutor.executeNode(varDecl, self.parentDataStore)

        self.allKeysStored.add(fullVariableKeyName)

    # Gets the concrete value of a variable by key
    def getVal(self, key: str) -> any:
        fullVariableKeyName = self.__getfullVariableNameByKey()
        return self.parentDataStore.getVariableValue(fullVariableKeyName)

    def removeVal(self, key: str):
        fullVariableKeyName = self.__getfullVariableNameByKey()
        self.__removeVal_internal(key)
        self.allKeysStored.remove(key)

    def __removeVal_internal(self, fullVarName: str):
        self.parentDataStore.removeVariable(fullVarName)
        self.allKeysStored.remove(fullVarName)

    # Gets the symbolic value of a variable by key
    def getSymbolicVariableValue(self, key: str) -> any:
        fullVariableKeyName = self.__getfullVariableNameByKey()
        return self.parentDataStore.getSymbolicVariableValue(fullVariableKeyName)

    def hasKey(self, key: str) -> bool:
        fullVariableKeyName = self.__getfullVariableNameByKey()
        returnFromDataStore = self.parentDataStore.hasVariable(fullVariableKeyName)
        returnFromInternal = key in self.allKeysStored

        assert returnFromInternal == returnFromInternal,"Desync !!!"
        return returnFromDataStore

    def isSymbolicDict(self) -> bool:
        return self.valuesAnnotation.isFromUserInput

    # Returns true/false depending whether a particular value of a key is symbolic
    def isVariableSymbolic(self, key: str) -> bool:
        # Is full dictionary symbolic ?
        res = self.isSymbolicDict()
        if res is True:
            return True

        # If not ,maybe this variable value only is
        fullVariableKeyName = self.__getfullVariableNameByKey()
        res = self.getSymbolicVariableValue(fullVariableKeyName)
        return res is not None

    # Returns a list with all content stored
    def getAllContent(self):
        return str(self.allKeysStored)

    # Creates a persistent iterator on
    """
    def getIterator(self) -> DictionaryWithStringKey_iterator:
        assert self.existingIter is None
        newIter = DictionaryWithStringKey_iterator(self)
        self.existingIter = newIter
        return newIter

    # Returns true if there is an iteration in progress
    def isIterationInProgress(self) -> bool:
        return self.existingIter is not None

    def clearIterator(self):
        assert self.existingIter is not None
        self.existingIter = None

    def __str__(self):
        if self.internalValue is None:
            return ""
        return str(self.internalValue)
    """

""""
if __name__ == "__main__":
    localDataTable = DataTable("pin_mocked_data.csv", lazyLoad=False)
    res = localDataTable.Rows.Item(0).Item(0)

    res2 = localDataTable.Rows.Item(0).Item("Pin:expected_pin")

    pass
"""