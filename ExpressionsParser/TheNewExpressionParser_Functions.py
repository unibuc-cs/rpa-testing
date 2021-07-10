import sys


def outPrettyPrint(args):
	print(args)


class DictionaryOfExternalCalls():
	def __init__(self):
		self.funcToCallForSymbol = {}
		self.defaultSetup()

	# Initialization of defaults , could be overriden by client with addFunctor function
	def defaultSetup(self):
		self.addFunctor("PrettyPrint", outPrettyPrint)

	def addFunctor(self, funcStr : str, funcMethod : any):
		self.funcToCallForSymbol[str] = funcMethod

	def getFunctor(self, funcStr : str):
		assert funcStr not in self.funcToCallForSymbol, f"There is no functor registered for {funcStr} !"
		return self.funcToCallForSymbol[funcStr]
""""
if __name__ == "__main__":
	# Simulate a dictionary of functions
	dictionaryOfExternalCalls = DictionaryOfExternalCalls()

"""