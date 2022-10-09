# MOCKING Functions, usually Global ones. For localized functions inside objects, even static methods inside objects,
# Please use the Parser_DataTypes file !
# The purpose of this file is to offer a default implementation of certain global functions.
# The client can then import its own function set here to extend the system

import sys
from Parser_DataTypes import DataTable, removeNamespacesFromName, DateTime

def outPrettyPrint(*args):
	outStr = "PrettyPrint: "
	for arg in args:
		outStr += str(arg) + " "
	print(outStr)

def outException(*args):
	outStr = "Exception: "

	# validate first fatal parameter
	assert isinstance(args[0], int), "First parameter must be 1 if fatal, or 0 if not"
	isFatal = int(args[0])

	# Show the message first
	for arg in args[1:]:
		outStr += str(arg) + " "
	print(outStr)

	# Judge if fatal
	if isFatal:
		print("Fatal exception")
	else:
		print("Not a fatal exception")

def LoadCSVDefault(*args):
	dataTable = DataTable(path=args[0], lazyLoad=False)
	return dataTable

def CreateRuntimeDateTime(*args):
	assert len(args) == 2, "You should provide first parameter as a string to the concrete data, the second is format "
	dateTime = DateTime(args[0], args[1])
	return dateTime

class DictionaryOfExternalCalls():
	def __init__(self):
		self.funcToCallForSymbol = {}
		self.defaultSetup()

	# Initialization of defaults , could be overriden by client with addFunctor function
	def defaultSetup(self):
		self.addFunctor("PrettyPrint", outPrettyPrint)
		self.addFunctor("Exception", outException)
		self.addFunctor("LoadCSV", LoadCSVDefault)
		self.addFunctor("DateTime", CreateRuntimeDateTime)

	def addFunctor(self, funcStr : str, funcMethod : any):
		self.funcToCallForSymbol[funcStr] = funcMethod

	def getFunctor(self, funcStr : str):
		isFuncInDictionary = funcStr in self.funcToCallForSymbol
		if isFuncInDictionary is False:
			# Try without namespace ?
			funcStr_withoutNamespace = removeNamespacesFromName(funcStr)
			if funcStr_withoutNamespace in self.funcToCallForSymbol:
				funcStr = funcStr_withoutNamespace
				isFuncInDictionary = True

		assert isFuncInDictionary, f"There is no functor registered for {funcStr} with/without namespace!"
		return self.funcToCallForSymbol[funcStr]

""""
if __name__ == "__main__":
	# Simulate a dictionary of functions
	dictionaryOfExternalCalls = DictionaryOfExternalCalls()

"""
