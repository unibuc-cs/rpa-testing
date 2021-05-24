
import myparser
import graphviz
import json
import sys

DataTypes = {
    'Int32':'Int',
    'String': 'String',
    'Boolean': 'Bool',
    "Double":'Real',
    "Decimal":'Decimal'
    }

 
def parseGraph(path, out_path):
    with open(path) as json_file:
        data = json.load(json_file)
        variables = data['variables']
        rname = data['displayName']
        z3Vars = {}
        z3Graph = {}
        for v in variables:
            #z3Vars[v] = DataTypes[variables[v]]
            z3Vars[rname+':'+v] = DataTypes[variables[v]]
            #z3Vars['Main:'+v] = DataTypes[variables[v]]
        graph = data['graph']
        for k in graph:
           
            #print(graph[k])
            # k is the node name 
            # graph[k] contains all info from a node
            # name = rname+':'+ k
            name = k
            #the guard will contain the expression parsed using myparser
            if graph[k]['expression'] == '':
                guard = 'None'
            else:
                ast = myparser.parse(graph[k]['expression'])
                guard = ast_to_string(ast,rname)
            # transitions contain a list of transitions 
            transitions=[]
            for trans in graph[k]['transitions']:
                transition = (trans['value'],trans['destination'])
                #transition = (trans['value'],rname+':'+trans['destination'])
                transitions.append(transition)
            if len(transitions) == 0:
                 z3Graph[name]="(\""+ str(guard) + "\"," + 'None' +")"
            elif len(transitions) == 1:
                 z3Graph[name]="(\"" + str(guard) + "\","+ str(transitions[0]) +")"
                  
            elif len(transitions) == 2:
                 z3Graph[name]= "(\"" + str(guard) + "\"," + "[" + str(transitions[0]) + "," +str(transitions[1]) +"]" +")"
                 
        print(z3Vars)
        print(z3Graph)
        z3GraphStr = ""
        for (k,v) in z3Graph.items():
            z3GraphStr = z3GraphStr + "\"" +k +"\"" + ": " + v +"\n" 
        data = "{" + "\"variables\"" + ": " +  str(z3Vars) +",\n" + 'graph'+": { \n"+ z3GraphStr + "}\n }"
        text_file = open(out_path, "w")
        text_file.write(data)
        text_file.close()
        '''
        with open(out_path, 'w') as outfile:
             json.dump(data, outfile,indent=4)
        '''
        '''
        with open(out_path) as json_file:
            data = json.load(json_file)
            print(data)
        '''
        # return z3Graph


def ast_to_string(localast,rname):
    # AST to string - using preorder 
    # to change for ternary operations
    if localast.token_type == myparser.TokenType.T_VAR:
        # localstr = 'V['+ localast.value+']'
        localstr = 'V['+rname+':'+ localast.value+']'
    else:
        localstr = localast.value
    st = ''
    dr = ''
    if len(localast.children) > 0 :
        
        if len(localast.children[0].children) == 0:
           st = str(ast_to_string(localast.children[0],rname))
        else:
           st =   "(" + str(ast_to_string(localast.children[0],rname))+")"
        if len(localast.children) ==2:
            if len(localast.children[1].children) == 0:
              dr = str(ast_to_string(localast.children[1],rname))
            else:
              dr =  "(" + str(ast_to_string(localast.children[1],rname))+")"
    
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
    path = '..\\Models\\' + sys.argv[1] # "SimpleBankLoan\Pin Check_202105121449166565.json"
    # rname = sys.argv[2] # Main
    out_path = path[:-5] + '_parsed.json'
    print(sys.argv)
    parseGraph(path, out_path)

'''
variables 
{'Main:loan': 'Int', 'Main:term': 'Int'}


graph

{'Main:loan_<_1000': ('(V[Main:loan]) < (1000)', [('False', 'Main:loan_in_[1000,100000]'), ('True', 'Main:Low_-_Volume_loan')]), 'Main:Low_-_Volume_loan': ('None', [('True', 'Main:term_in_years_<_5')]), 'Main:loan_in_[1000,100000]': ('And(((V[Main:loan]) >= (1000)),((V[Main:loan]) < (100000)))', [('False', 'Main:High_-_Volume_loan'), ('True', 'Main:Mid_-_Volume_loan')]), 'Main:Mid_-_Volume_loan': ('None', [('True', 'Main:term_in_years_<_5')]), 'Main:High_-_Volume_loan': ('None', [('True', 'Main:term_in_years_<_5')]), 'Main:term_in_years_<_5': ('(V[Main:term]) < (5)', [('False', 'Main:Long_term'), ('True', 'Main:Short_-_Term')]), 'Main:Short_-_Term': ('None', [('True', 'Main:Output_rate_')]), 'Main:Long_term': ('None', [('True', 'Main:Output_rate_')]), 'Main:sinkT': ('V[Main:True]', []), 'Main:sinkF': ('V[Main:True]', [])}


{'Main:pin': 'String'}
{'Main:pinTest': ('(V[Main:pin]) == ("1234")', [('False', 'Main:retryCheck'), ('True', 'Main:succeedCheck')]), 'Main:checkPin': ('None', [('True', 'Main:pinTest')]), 'Main:retryCheck': ('None', [('True', 'Main:canRetry')]), 'Main:canRetry': ('(V[Main:tryNumber]) < (3)', [('False', 'Main:faledCheck'), ('True', 'Main:checkPin')]), 'Main:sinkT': ('V[Main:True]', 'None'), 'Main:sinkF': ('V[Main:True]', 'None')}


'''
#test_parser('(1+7)*(9+2)')
#test_parser('(6 < a)' )

#test_parser('term < 5' )
#test_parser('(loan >= 1000) and (loan < 100000)' )


