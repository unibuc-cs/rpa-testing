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
import sys
import pandas as pd
from typing import Dict

# Each entry is a dict from variable name to its value
class InputSeed():
    DEFAULT_PRIORITY = 0
    def __init__(self):
        self.content : Dict[str, any] = {}
        self.priority : int = 0

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

    def NumIems(self) -> int:
        return self.data.shape[0]

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
    def Columns(self):
        self._checkInit()
        return DataTable_ColumnsView(self.data)

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

""""
if __name__ == "__main__":
    localDataTable = DataTable("pin_mocked_data.csv", lazyLoad=False)
    res = localDataTable.Rows.Item(0).Item(0)

    res2 = localDataTable.Rows.Item(0).Item("Pin:expected_pin")

    pass
"""