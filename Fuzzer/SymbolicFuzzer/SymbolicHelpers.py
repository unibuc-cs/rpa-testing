# TODO Ciprian multiprocessing: https://stackoverflow.com/questions/8533318/multiprocessing-pool-when-to-use-apply-apply-async-or-map
import copy

import z3
from z3 import *
import heapq
from typing import List, Dict, Set, Tuple
from Parser_ASTNodes import *
from WorkflowGraphBaseNode import BaseSymGraphNode, SymGraphNodeFlow, SymGraphNodeBranch
from SymbolicHelpers import *
import csv

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

    # Gets the NOT expression out of an initial condition to solve
    @staticmethod
    def getInverseOfSymbolicExpresion(condToSolve):
        condToSolve = 'Not(' + condToSolve + ')'
        return condToSolve

    # Converts a string expression (Z3 kind of) to a Z3 full node expression
    @staticmethod
    def convertStringExpressionTOZ3(condToSolve, contextDataStore):
        cond = eval(condToSolve)
        return cond


class ASTFuzzerNode_VariableDecl(ASTFuzzerNode):
    """ E.g.
    "local_number_retries": {
        "Type": "Int32",
        "Default": "0"
    },
    """

    # Given the type of the variable as a string and the expression containing the default value, get the default object value
    @staticmethod
    def getDefaultValueFromExpression(varTypeName: str, defaultExpression: str) -> any:
        res = None
        if varTypeName == "Int32":
            res = 0 if defaultExpression is None else int(defaultExpression)
        elif varTypeName == 'Boolean':
            res = False if (defaultExpression == None or defaultExpression == 'false' or defaultExpression == 'False'
                  or int(defaultExpression) == 0) else True
        else:
            raise NotImplementedError("Do it yourself !!")

        return res


    # Will put the variabile in the datastore
    def __init__(self, varName : str, typeName : str, **kwargs):
        super().__init__(ASTFuzzerNodeType.VARIABLE_DECL)
        self.typeName = typeName
        self.defaultValue = kwargs['defaultValue'] if 'defaultValue' in kwargs else None
        self.varName = varName


        # self.value represents the CURRENT concrete value, while self.symbolicValue represents the Z3 symbolic value associated with it
        self.symbolicValue = None
        self.value = None

        # Fill the annotations
        self.annotation = VarAnnotation()
        annotationTag = kwargs.get('annotation')
        if annotationTag is not None:
            if 'bounds' in annotationTag:
                self.annotation.bounds = int(annotationTag['bounds'])
            if 'min' in annotationTag:
                self.annotation.min = int(annotationTag['min'])
            if 'max' in annotationTag:
                self.annotation.max = int(annotationTag['max'])
            if 'pattern' in annotationTag:
                self.annotation.pattern = str(annotationTag['pattern'])
            if 'userInput' in annotationTag:
                valSpec = annotationTag['userInput']
                self.annotation.isFromUserInput = 1 if (valSpec == 'True' or valSpec == '1' or valSpec == 'true') else 0
                if self.annotation.isFromUserInput == 1:
                    assert self.defaultValue == None, "In the case of variables coming as inputs you can't put a default value !"

        # Build the variabile symbolic and default value depending on its type
        if typeName == "Int32":
            self.value = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName=typeName,
                                                                                  defaultExpression=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)

        elif typeName == 'Int32[]':
            self.value = FuzzerArray.CreateArray('Int32', annotation=self.annotation, defaultValue=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == 'String[]':
            self.value = FuzzerArray.CreateArray('String', annotation=self.annotation, defaultValue=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == "List":
            assert self.annotation is None or self.annotation.isFromUserInput is False, \
                "List type is not supported for symbolic execution since its element could be anything !!. So no annotation please that involves symbolic"

            self.value = FuzzerList.Create(annotation=self.annotation, defaultValue=self.defaultValue)

        elif typeName == 'Boolean':
            self.value = ASTFuzzerNode_VariableDecl.getDefaultValueFromExpression(varTypeName=typeName,
                                                                                  defaultExpression=self.defaultValue)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == "DataTable":
            lazyLoad = True if 'lazyLoad' not in kwargs else kwargs['lazyLoad']
            path = self.defaultValue
            self.value = DataTable(path=path, lazyLoad=lazyLoad)

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)

        elif typeName == "DataTable_iterator":
            assert self.defaultValue, "You must specify a default value in this case"

            self.value = self.defaultValue
        elif typeName == "String":
            self.value = str(self.defaultValue) if self.defaultValue == None else ""

            if self.annotation.isFromUserInput:
                self.symbolicValue = SymbolicExecutionHelpers.createVariable(typeName=typeName, varName=varName, annotation=self.annotation)
        elif typeName == "Float":
            raise NotImplementedError("Not yet")
        else:
            raise  NotImplementedError(f"Unknown decl type {typeName}")

class SMTPath:
    def __init__(self,
                 parentWorkflowGraph,
                 initial_conditions_smt : List[any], # The initial set of conditions for the state of the path when being created
                 dataStore,
                 start_nodeId,              # The starting node id to consider expanding the path
                 debugFullPathEnabled : bool, # If full path debugging is supported
                 debugNodesHistoryExplored: List[str]): # The nodes considered as explored by the path already, when this is created (note could be new or from a BRANCHING effect !)

        # The parent workflow graph that this path is working on
        self.parentWorkflowGraph = parentWorkflowGraph

        # The conditions in the Z3 format needed for this path (all not only initial !)
        self.conditions_smt : List[str] = initial_conditions_smt

        # Only valid for concolic exection, A dict from the index of the condition in self.conditions_smt to a boolean
        # value representing True if the branch was taken in the execution path or false otherwise.
        self.concolicBranchTaken : Dict[int, bool] = {} # index from condition_smt to {True/False}

        # The dataStore this object is iterating on
        self.dataStore = dataStore

        # The priority of this path..
        self.priority = None

        # Current SMT solver, could be none for paths that are not actually used yet
        self.currentSolver : Solver = None

        # This is the starting node of this path.
        self.startNode_Id : BaseSymGraphNode = start_nodeId

        # This is the current node iterating in in the workflow
        self.currNode : BaseSymGraphNode = None

        # This is the level of this path in the branching tree
        self.levelInBranchTree = 0

        # Will be set to true if this branch is considered as failed
        self.failed = False

        # If enabled, it will store/output the entire path found.
        # Could be very costly especially for a long run !!
        self.debugFullPathEnabled : bool = debugFullPathEnabled

        # If debugFullPathEnabled, this will keep the ordered set of nodes explored by the path
        self.debugNodesExplored : List[str] = []

        self.debugNumPathsSolvableFound = 0


    # Init the execution context
    # TODO Ciprian: init a context solver from existing one maybe ?
    def initExecutionContext(self):
        # Set the instance of the current node that this path is continue working on
        self.currNode = self.parentWorkflowGraph.getNodeInstanceById(self.startNode_Id)
        assert self.currNode != None, "Current node couldn't be solved !!!"

        # Initialize the solve, put all the assertions in
        self.currentSolver = Solver()
        for z3Cond in self.conditions_smt:
            self.currentSolver.add(z3Cond)

    # Get the current node iterating in in the workflow
    def getNode(self) -> BaseSymGraphNode:
        return self.currNode

    def isFinished(self) -> bool:
        return self.currNode is None

    # Advance the node towards the next one in the workflow operation
    def advance(self, branchToFollowNext : str = None):
        if branchToFollowNext != None:
            assert isinstance(self.currNode, SymGraphNodeBranch)
            assert isinstance(branchToFollowNext, str)
            assert branchToFollowNext in self.currNode.valuesAndNextInst, f"The result is not in the list of branch decisions {str(branchToFollowNext)}!"
            self.currNode = self.currNode.valuesAndNextInst[str(branchToFollowNext)]
        else:
            assert isinstance(self.currNode, SymGraphNodeFlow)
            self.currNode = self.currNode.nextNodeInst

        if self.currNode and self.debugFullPathEnabled:
            self.debugNodesExplored.append(self.currNode.id)

    # Knowing the current node executing, return what is the next node instance based on a given branch result
    def getNextNodeOnBranchResult(self, branchToFollowNext : str = None) -> BaseSymGraphNode:
        assert self.currNode != None and isinstance(self.currNode, SymGraphNodeBranch), "Incorrect current node setup"
        assert branchToFollowNext in self.currNode.valuesAndNextInst, f"The result is not in the list of branch decisions {str(branchToFollowNext)}!"
        return self.currNode.valuesAndNextInst[str(branchToFollowNext)]

    # Checks if the model is solvable with a new condition added in
    def isNewConditionSolvable(self, newConditionInZ3) -> bool:
        assert self.currentSolver, "Solver was not initialized ! Is this expected ??"
        self.currentSolver.push()
        self.currentSolver.add(newConditionInZ3)
        res = self.currentSolver.check()

        # DEBUG CODE DO NOT ENABLE ON RELEASE !!
        """
        if res != None and res != z3.unsat:
            m = self.currentSolver.model()
            for d in m.decls():
                print(f"{d.name()}={m[d]}")
        """

        self.currentSolver.pop()
        return res

    # Add a new condition to this path: we expect it to be feasible in general for optimal results, but not necessarily
    def addNewBranchLevel(self, newConditionInZ3, executeNewConditionToo, concolicEval=None):
        self.conditions_smt.append(newConditionInZ3)

        # IF we add a concolic branch, and we have a taken evaluation that is can be subject to change,
        # concolicEval will be not None (or should be !)
        # In this case we store in the dictionary the value taken
        if concolicEval is not None:
            assert isinstance(concolicEval, bool), "If given, we are expecting either a True or False take branch"
            indexOfCondition = len(self.conditions_smt) - 1
            self.concolicBranchTaken[indexOfCondition] = concolicEval

        # Add the new conditions to the solver
        if executeNewConditionToo == True:
            self.currentSolver.add(newConditionInZ3)

        # DEBUG code vor simpplification methods. DO NOT ENABLE ON RELEASE
        """
        if (len(self.conditions_z3) == 3):
            fullAndExpr = And(self.conditions_z3[0], self.conditions_z3[1], self.conditions_z3[2])
        exprSimpl = z3.simplify(fullAndExpr, elim_and=True)

        x = Int('x')
        y = Int('y')
        print(simplify(x + y + 2 * x + 3))
        print(simplify(x < y + x + 2))
        print(simplify(And(x + 1 >= 3, x ** 2 + x ** 2 + y ** 2 + 2 >= 5), elim_and=True))

        g = Goal()
        g.add(And(x >= 3, x >= 10))
        print(g)

        t1 = Tactic('simplify')
        print(t1(g))
        t2 = Repeat(t1)
        print(t2(g))

        # Increase also the level in the branch tree evaluation
        self.levelInBranchTree += 1
        #"""

    # startingNodeId - THe next starting node to run this path from
    # isQueuedNode - Just a hint to know if this path has been put on a delayed queue for later execution or it is starting executing now
    def setStartingNodeId(self, startingNodeId, isQueuedPathNode : bool):
        self.startNode_Id = startingNodeId

        # Add the starting node
        if self.debugFullPathEnabled and isQueuedPathNode:
            self.debugNodesExplored.append(self.startNode_Id)

    # Forcing the "isFinished" to return true starting now...
    # Normally this function is called when the path is not feasible anymore or it is feasibile or we want it to end (fill result in)
    def forceFinish(self, withFail : bool):
        self.currNode = None
        self.failed = withFail

    # Based on the current solver and set of conditions added to it, get the SMT model with all declarations
    # If not feasibile it returns None
    def getSolvedModel(self):
        if not self.currentSolver.check():
            return None
        return self.currentSolver.model()

    def __copy__(self):
        # For now, just create a new type and move dictionaries...
        newObj = type(self)(self.parentWorkflowGraph, self.conditions_z3, self.dataStore,
                            self.startNode_Id,
                            self.debugFullPathEnabled, self.debugNodesExplored)
        newObj.__dict__.update(self.__dict__)
        return newObj

    def __deepcopy__(self, memodict={}):
        # First, take all values from the other..
        newObj = type(self)(self.parentWorkflowGraph, [], None, None, False, [])
        newObj.__dict__.update(self.__dict__)

        # Then invalidate solver, current node
        newObj.currentSolver = None
        newObj.currNode = None
        newObj.startNode_Id = None

        # Duplicate the conditions
        newObj.conditions_smt = copy.deepcopy(self.conditions_smt)
        newObj.dataStore = copy.deepcopy(self.dataStore)
        newObj.debugNodesExplored = copy.deepcopy(self.debugNodesExplored)
        newObj.concolicBranchTaken = copy.deepcopy(self.concolicBranchTaken)
        return newObj

    def __lt__(self, other):
        return self.priority > other.priority


# A priority queue data structure for holding inputs by their priority
class SMTWorklist:
    def __init__(self):
        self.internalHeap = []

    def extractPath(self):
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
