# z3 playground
# Other nice in #https://ericpony.github.io/z3py-tutorial/guide-examples.htm
# str to assertions

from z3 import *

def demo_bitVecs():
    # Create to bit-vectors of size 32
    x, y = BitVecs('x y', 32)

    solve(x + y == 2, x > 0, y > 0)

    # Bit-wise operators
    # & bit-wise and
    # | bit-wise or
    # ~ bit-wise not
    solve(x & y == ~y)

    solve(x < 0)

    # using unsigned version of <
    solve(ULT(x, 0))

def demo_loanModel():
    loan = Int('loan')
    term = Int('term')

    condA = "loan < 1000"
    condB = "And(loan >= 1000, loan < 10000)"
    condC = "term < 5"

    conds_str = [condA,condB,condC]
    conds_z3 = [eval(s) for s in conds_str]

    sol = Solver()
    sol.add(conds_z3[1])
    sol.add(Not(conds_z3[2]))
    isSolution = sol.check()
    #print(isSolution)
    if isSolution and isSolution != z3.unsat:
        m = sol.model()
        for d in m.decls():
            print(f"{d.name()}={m[d]}")
    else:
        print("No solution exists")

# Select an index from an array has a certain given target value
# E.g. Declare an array [12, 45, 66, 34]. Get a model that finds index x with a given
# target value = 45 => k = 1
def demoArraySelection():
    s = Solver()
    array = [12, 45, 66, 34]
    targetValue = 45
    A = Array('A', IntSort(), IntSort())
    i = 0
    for i,v in enumerate(array):
        A = Store(A, i, v)
        #print(A.sexpr())

    x = Int('x')
    s.add(x >= 0)
    s.add(x < len(array))
    s.add(Select(A,x) == targetValue)

    # Two ways to debug !
    print("solver sexpr", s.sexpr())
    for assertion in s.assertions():
        print(assertion.sexpr())

    if s.check() == sat:
        print (s.model())
    else:
        print("Not found")


# Demo infer position K to delete in a vector to give a certain output vector given an initial
# input vector.
# E.g.Given an input integer array I=[1,2,3,4,5], and an output integer array O=[1,2,4,5],
# Infer that we need to delete index k = 2
# Logically: Delete(I,O) =  (ForAll 0<=x<k, O[x] = I[x] ) and (ForAll k<=x<length(I)-1, O[x] = I[x+1]) is tru

def demoInferOutArray():
    x = Int('x')
    y = Int('y')
    k = Int('k')

    s = Solver()

    I = Array('I', IntSort(), IntSort())
    O = Array('O', IntSort(), IntSort())
    I = Store(I, 0, 1)
    I = Store(I, 1, 2)
    I = Store(I, 2, 3)
    I = Store(I, 3, 4)
    I = Store(I, 4, 5)

    O = Store(O, 0, 1)
    O = Store(O, 1, 2)
    O = Store(O, 2, 3)
    O = Store(O, 3, 4)

    s.add(k >= 0)
    s.add(k < 4)
    s.add(And(
            ForAll([x], Implies(And(x >= 0,x<k), Select(O,x)==Select(I,x))),
            ForAll([x], Implies(And(y > k, y<4), Select(O,y)==Select(I,y+1)))
            ))
    print(s.check())
    if s.check() == z3.sat:
        print(s.model())

if __name__ == "__main__":
    #demoArraySelection()
    demoInferOutArray()

