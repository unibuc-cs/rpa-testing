import sys

class DictionaryOfExternalCalls():
	def __init__(self):
		self.funcToCallForSymbol = {}
		self.defaultSetup()

	# Initialization of defaults , could be overriden by client with addFunctor function
	def defaultSetup(self):
		self.addFunctor("ToString", str)
		self.addFunctor("Int32.Parse", int)

	def addFunctor(self, funcStr : str, funcMethod : any):
		self.funcToCallForSymbol[str] = funcMethod


""""
if __name__ == "__main__":
	# Simulate a dictionary of functions
	dictionaryOfExternalCalls = DictionaryOfExternalCalls()

"""