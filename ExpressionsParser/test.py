
import myparser
import graphviz
import json
import sys

DataTypes = {
    'Int32':'Int'
    }

 
def parseGraph(path):
    with open(path) as json_file:
        data = json.load(json_file)
        variables = data['variables']
        z3Vars = {}
        z3Graph = {}
        for v in variables:
            z3Vars['V['+v+']'] = DataTypes[variables[v]]
            #z3Vars['Main:'+v] = DataTypes[variables[v]]
        graph = data['graph']
        for k in graph:
           
            #print(graph[k])
            # k is the node name 
            # graph[k] contains all info from a node
            name = k
            #the guard will contain the expression parsed using myparser
            if graph[k]['expression'] == '':
                guard = 'None'
            else:
                ast = myparser.parse(graph[k]['expression'])
                guard = ast_to_string(ast)
            # transitions contain a list of transitions 
            transitions=[]
            for trans in graph[k]['transitions']:
                transition = (trans['value'],trans['destination'])
                transitions.append(transition)
            
            z3Graph[name]=(guard,transitions)
       
        return z3Graph


def ast_to_string(localast):
    # AST to string - using preorder 
    # to change for ternary operations
    localstr = localast.value
   
    if len(localast.children) > 0 :
        localstr = localstr + '(' +  "(" + str(ast_to_string(localast.children[0]))+")"
        if len(localast.children) ==2:
              localstr = localstr +','+ "(" + str(ast_to_string(localast.children[1]))+")"
        localstr = localstr +')'
    return localstr

def test_parser(inputstring):
    ast = myparser.parse(inputstring)
    graphviz.label(ast)
    graphviz.to_graphviz(ast)
 
    
 

if __name__ == '__main__':
    path = 'D:\parser-master\inputfile.json'
    print(parseGraph(path))


#test_parser('(1+7)*(9+2)')
#test_parser('(6 < a)' )

#test_parser('term < 5' )
#test_parser('(loan >= 1000) and (loan < 100000)' )


