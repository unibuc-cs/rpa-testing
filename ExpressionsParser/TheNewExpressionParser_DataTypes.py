import sys
import pandas as pd

# From str to API object
def str2Class(str):
    return getattr(sys.modules[__name__], str)

# An Object kind of thing that has a value and can be converted to values
# Purpose to call obj.ToString() and some others
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

	def __call__(self):
		return self


class DataTable_ColumnsView:
	def __init__(self, data):
		self.data : pd.DataFrame = data

	def Item(self, index) -> DataTable_Column:
		return DataTable_Column(self.data[index])

	def __call__(self):
		return self

class DataTable:
	def __init__(self, **kwargs):
		self.path = kwargs["path"]
		self.data = None
		self.lazyLoad = kwargs["lazyLoad"]
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
	def InsertNewRow(self, rowData):
		self.data.append(rowData,ignore_index=True,sort=False)
		return True

	# Saves the current datatable to a file (could be the same or other)
	def SaveToCSV(self, filePath : str):
		self.data.to_csv(path_or_buf=filePath, index=False)

	def __load(self):
		# TODO
		self.data = pd.read_csv(self.path)

""""
if __name__ == "__main__":
	localDataTable = DataTable("pin_mocked_data.csv", lazyLoad=False)
	res = localDataTable.Rows.Item(0).Item(0)

	res2 = localDataTable.Rows.Item(0).Item("Pin:expected_pin")

	pass
"""