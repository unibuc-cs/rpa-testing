import math
import random
import os
from WorkflowGraph import NodeTypes


class EFSMTransition:
    def __init__(self):
        self.left = ""
        self.right = ""
        self.id = 0
        self.guard = ""
        self.assignment = ""


class EFSM:
    def __init__(self, wfgraph):
        self.transitions = {}  # Hashmap String, EFSMTransition
        self.stateTransNum = {} # HashMap String - Int
        self.states = []
        self.stateAndTransitions = {}
        self.ranges={}
        # to add other variabiles to use

        # convert wfGraph into an EFSM
        # we need the following elements
        # transitions - a map of Int-EFSMTransition
        # transNames - the names of the transitions - we don't have names, just ids from 0 to nr of transitions
        # states - the names of the states
        # stateTransNum - the number of transitions exiting each state
        # startState
        # statesAndTransitions

        # contextVars - global variables
        # ranges and LMC - are computed based on StateTRansNum

        # EFSM has the following
        self.startState = wfgraph.entryTestNodeId

        graphInst = wfgraph.graphInst
        dsVars = vars(wfgraph.dataStoreTemplate)
        self.contextVars = dsVars["Values"]
        print(self.contextVars)

        for node in graphInst.nodes:
            self.states.append(node.id)
            self.stateAndTransitions[node.id] = []
            self.stateTransNum[node.id] = 0
        i = 0
        for edge in graphInst.edges:
            transition: EFSMTransition = EFSMTransition()
            transition.left = edge[0]
            transition.right = edge[1]
            transition.id = i
            i = i + 1

            transition.guard = ""  # the expression.
            transition.assignment = ""
            if edge[0].nodeType == NodeTypes.BRANCH_NODE:
                truth_value = edge[0].valuesAndNext.values()
                my_dict = edge[0].valuesAndNext
                key_list = list(my_dict.keys())
                val_list = list(my_dict.values())

                # print key with val 100
                position = val_list.index(str(edge[1]))
                if key_list[position]:
                    transition.guard = str(edge[0].expression)
                else:
                    transition.guard = "( "+ str(edge[0].expression) + ") == False"

            # if we have a flow node -> guard checks the expression for true value --- actually it seems to be an asignment???
            # if we have branch then each transition has a guard,
            # the true transition gets the expression and the false transition gets the negation of the expression

            elif edge[0].nodeType == NodeTypes.FLOW_NODE:
                transition.assignment = str(edge[0].expression)
            self.transitions[transition.id] = transition
            self.stateTransNum[transition.left.id] = self.stateTransNum[transition.left.id] + 1
            self.stateAndTransitions[transition.left.id].append(transition.id)

        # add this to transitions
        self.LMC = self.findlmc()

        for st in self.stateTransNum:

            if self.stateTransNum[st] == 0 :
                self.ranges[st] = 0
            else:
                self.ranges[st] = self.LMC // self.stateTransNum[st]

    def findlmc(self):
        arr = self.stateTransNum
        ans = 1
        for v in arr:
            if arr[v] > 0 :
                ans = (arr[v]*ans) // (math.gcd(arr[v],ans))
        return ans

    def ftpFromIntList(self, chrom):
        i = 0
        tp = []
        currentState = self.states.index(self.startState)
        for i in range(len(chrom)):
            nx = chrom[i]
            currentTransition = self.getTransFromIntList(nx, currentState)
            tp.append(currentTransition)
            trans : EFSMTransition = self.transitions.get(currentTransition)
            if trans is None:
                return None
            out = trans.right

            currentState = self.states.index(out)

        return tp

    def getTransFromIntList(self, nx, currentNode):
        currentRange = self.ranges[currentNode]
        trans = self.stateAndTransitions[currentNode]
        for i in range(self.stateTransNum[currentNode]):
            if nx < currentRange * ( i+1):
                return trans[i]
        return None

    def generateRandomPath(self):
        currentNode = self.startState
        currentTransitions = self.stateAndTransitions[currentNode]
        tp = []
        while len(currentTransitions) > 0:
            nr = random.uniform(1, self.LMC-1)
            currentTransition = self.getTransFromIntList(nr, str(currentNode))
            tp.append(currentTransition)
            trans: EFSMTransition = self.transitions.get(currentTransition)
            if trans is None:
                return None
            out = trans.right
            currentNode = out
            currentTransitions = self.stateAndTransitions[str(currentNode)]
        return tp

    def tpPrettyPrint(self, tp):
        for p in tp:
            trans = self.transitions.get(p)
            print(str(trans.left) + " -> " + str(trans.right))
    def saveAsFile(self,tp, args):
        self.outputTests_PrefixFile = args.outputTests_PrefixFile
        outFolder = args.modelBasePath
        outfile = os.path.join(outFolder, "generatedPath.txt")
        # Setup the output files stuff
        f= open(outfile,"w+")
        for p in tp:
            trans = self.transitions.get(p)
            f.write(str(trans.left) + " -> " + str(trans.right) +"\n")
        f.close()


class EFSM_Tester:
    def __init__(self, wfGraph):
        self.wfGraph = wfGraph  # DiGraph
        # print(wfGraph)
        self.efsm: EFSM = EFSM(wfGraph)

    def solve(self, args):
        # generate a random path
        tp = self.efsm.generateRandomPath()
        print(tp)
        self.efsm.tpPrettyPrint(tp)
        self.efsm.saveAsFile(tp, args)