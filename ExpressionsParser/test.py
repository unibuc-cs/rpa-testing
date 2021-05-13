
import myparser
import graphviz
import json
import sys

DataTypes = {
    'Int32':'Int'
    }

 
def parseGraph(path, rname):
    with open(path) as json_file:
        data = json.load(json_file)
        variables = data['variables']
        z3Vars = {}
        z3Graph = {}
        for v in variables:
            z3Vars['V['+rname+':'+v+']'] = DataTypes[variables[v]]
            #z3Vars['Main:'+v] = DataTypes[variables[v]]
        graph = data['graph']
        for k in graph:
           
            #print(graph[k])
            # k is the node name 
            # graph[k] contains all info from a node
            name = rname+':'+ k
            #the guard will contain the expression parsed using myparser
            if graph[k]['expression'] == '':
                guard = 'None'
            else:
                ast = myparser.parse(graph[k]['expression'])
                guard = ast_to_string(ast)
            # transitions contain a list of transitions 
            transitions=[]
            for trans in graph[k]['transitions']:
                transition = (trans['value'],rname+':'+trans['destination'])
                transitions.append(transition)
            
            z3Graph[name]=(guard,transitions)
       
        return z3Graph


def ast_to_string(localast):
    # AST to string - using preorder 
    # to change for ternary operations
    localstr = localast.value
    st = ''
    dr = ''
    if len(localast.children) > 0 :
        st =   "(" + str(ast_to_string(localast.children[0]))+")"
        if len(localast.children) ==2:
              dr =  "(" + str(ast_to_string(localast.children[1]))+")"
    
    if st == '' and dr == '':
        localstr = localstr 
    elif st == '' and dr != '':
        localstr = localstr + ' ' + dr 
    elif st != '' and dr == '':
        localstr = localstr + ' ' + st
    elif localast.value in ["And",'Or']:
        localstr = localstr + '(' + st + ',' + dr + ')'
    else:
        localstr = st + ' ' + localstr + ' ' + dr
    return localstr

def test_parser(inputstring):
    ast = myparser.parse(inputstring)
    graphviz.label(ast)
    graphviz.to_graphviz(ast)
 
    
 

if __name__ == '__main__':
    path = 'D:\parser-master\inputfile.json'
    print(parseGraph(path, "Main"))


#test_parser('(1+7)*(9+2)')
#test_parser('(6 < a)' )

#test_parser('term < 5' )
#test_parser('(loan >= 1000) and (loan < 100000)' )


