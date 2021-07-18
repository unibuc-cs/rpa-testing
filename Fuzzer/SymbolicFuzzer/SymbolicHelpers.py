import z3
from z3 import *

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
            raise NotImplementedError("Pattern support is not yet implemented. DO IT DO NOW FORGET !")
        elif typeName == "Float":
            res = z3.Real(varName)
        elif typeName == 'Bool':
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