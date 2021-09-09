import z3
from z3 import *
import heapq
from typing import List, Dict, Set, Tuple

# TODO: interface / Z3 only ?
class SymbolicExecutionHelpers:
    def __init__(self):
        pass

    # Given a sort as a string convert to a real Z3 object sort
    @staticmethod
    def __fromStrSortToZ3Sort(strSort : str):
        if strSort == 'Int':
            return z3.IntSort()
        elif strSort == 'Bool':
            return z3.BoolSort()
        elif strSort == 'String':
            return z3.StringSort()
        elif strSort == 'Real':
            return z3.RealSort()
        elif strSort == 'Array':
            return z3.ArraySort()
        elif strSort == 'BitVec':
            return z3.BitVecSort()
        else:
            assert f"Can't solve the given {strSort} type !"
            return None
        return None


    # Creates a symbolic variabile given its name, type and annotation
    @staticmethod
    def createVariable(typeName, varName, annotation):
        res = None
        if typeName == "Int32":
            res =  z3.Int(varName)
        elif typeName == "String":
            res = z3.String(varName)
          #  raise NotImplementedError("Pattern support is not yet implemented. DO IT DO NOW FORGET !")
        elif typeName == "Float":
            res = z3.Real(varName)
        elif typeName == 'Bool':
            res = z3.Bool(varName)
        elif typeName == 'Boolean':
            res = z3.Bool(varName)
        elif typeName in ('Int32[]', 'Float[]', 'Bool[]'):
            res = None
            if annotation.bounds is not None: # The BEST way to deal with arrays ! know your bounds
                if typeName == "Int32[]":
                    res = z3.IntVector(varName, annotation.bounds) # Bounds must exist in this case !
                elif typeName == "Bool[]":
                    res = z3.BoolVector(varName, annotation.bounds)
                elif typeName == "Float[]":
                    res = z3.RealVector(varName, annotation.bounds)
                else:
                    raise NotImplementedError()
            else: # If REALLY NOT..then Array theory works too...
                indexSort = "Int"
                valuesSort = None

                possibleValuesSorts_keys = ["Int", "Bool", "Float"]
                possibleValuesSorts_values = ["Int", "Bool", "Real"]

                for vs_key_index, vs_key_str in enumerate(possibleValuesSorts_keys):
                    if vs_key_str in typeName:
                        valuesSort = possibleValuesSorts_values[vs_key_index]
                        break
                assert valuesSort, f"Couldn't find a values sort for type name {typeName}"

                indexSort = SymbolicExecutionHelpers.__fromStrSortToZ3Sort(indexSort)
                valuesSort = SymbolicExecutionHelpers.__fromStrSortToZ3Sort(valuesSort)
        elif typeName == "DataTable":
            raise NotImplementedError("Not supported yet but soon..")
        elif typeName == 'Function':
            raise NotImplementedError()
            pass  # TODO fix later
        else:
            raise NotImplementedError()

        return res

class SMTPath:
    def __init__(self):
        self.conditions : List[str] # The conditions in the Z3 format needed for this path
        # Add many others...

        self.priority = None # the priority of this path..

    def __lt__(self, other):
        return self.priority > other.priority


# A priority queue data structure for holding inputs by their priority
class SMTWorklist:
    def __init__(self):
        self.internalHeap = []

    def extractInput(self):
        if self.internalHeap:
            next_item = heapq.heappop(self.internalHeap)
            return next_item
        else:
            return None

    def addPath(self, newPath: SMTPath):
        heapq.heappush(self.internalHeap, newPath)

    def __str__(self):
        str = f"[{' ; '.join(inpStr.__str__() for inpStr in self.internalHeap)}]"
        return str

    def __len__(self):
        return len(self.internalHeap)
