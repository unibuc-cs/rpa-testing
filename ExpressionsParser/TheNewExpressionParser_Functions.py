import sys


def outPrettyPrint(*args):
	outStr = "PrettyPrint: "
	for arg in args:
		outStr += str(arg) + " "
	print(outStr)


class DictionaryOfExternalCalls():
	def __init__(self):
		self.funcToCallForSymbol = {}
		self.defaultSetup()

	# Initialization of defaults , could be overriden by client with addFunctor function
	def defaultSetup(self):
		self.addFunctor("PrettyPrint", outPrettyPrint)

	def addFunctor(self, funcStr : str, funcMethod : any):
		self.funcToCallForSymbol[funcStr] = funcMethod

	def getFunctor(self, funcStr : str):
		assert funcStr in self.funcToCallForSymbol, f"There is no functor registered for {funcStr} !"
		return self.funcToCallForSymbol[funcStr]
""""
if __name__ == "__main__":
	# Simulate a dictionary of functions
	dictionaryOfExternalCalls = DictionaryOfExternalCalls()

"""