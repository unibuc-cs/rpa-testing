import myparser
import graphviz
import json
import sys
import pickle
import os

DataTypes = {
    'Int32': 'Int',
    'String': 'String',
    'Boolean': 'Bool',
    "Double": 'Real',
    "Decimal": 'Real'
}

Colors = ["red", "blue", "yellow", "green", "violet", "orange"]


def parseGraph(path, out_path):
    with open(path) as json_file:
        data = json.load(json_file)
        variables = data['variables']
        rname = data['displayName']
        out_path = out_path + rname + ".txt"
        z3Vars = {}
        z3Graph = {}
        for v in variables:
            # z3Vars[v] = DataTypes[variables[v]]
            z3Vars[rname + ':' + v] = DataTypes[variables[v]]
            # z3Vars['Main:'+v] = DataTypes[variables[v]]
        graph = data['graph']

        for k in graph:

            # DEBUG
            if "Assign_20" in k:
                a = 3
                a += 1

            # print(graph[k])
            # k is the node name
            # graph[k] contains all info from a node
            # name = rname+':'+ k
            name = k
            # the guard will contain the expression parsed using myparser
            if graph[k]['expression'] == '':
                guard = 'None'
            else:
                ast = myparser.parse(graph[k]['expression'])
                guard = "\"" + ast_to_string(ast, rname) + "\""

            # assigments
            assign_list = graph[k].get("variableAssignments")
            assignments = []
            if assign_list:
               assignment_var = assign_list['to']
               assignment_exp = assign_list['value']
               ast_v = myparser.parse(assignment_var)
               ast_e = myparser.parse(assignment_exp)
               if ast_e.token_type == myparser.TokenType.T_VAR:
                    ast_e_str = ast_to_string(ast_e, rname)
               else:
                   ast_e_str =  ast_to_string(ast_e, rname)
               assignments.append((ast_to_string(ast_v, rname), ast_e_str))

            #invoked wf args
            invokedWorkflow = graph[k].get("invokedWorkflow")
            if invokedWorkflow:
                variableMappings = graph[k]["variableMappings"]
                invokedWorkflowDisplayName = graph[k].get("invokedWorkflowDisplayName")
                print(invokedWorkflowDisplayName)
                if invokedWorkflowDisplayName == None:
                    invokedWorkflowDisplayName="Wf2"
                for var in variableMappings:
                    type = var['argumentType']
                    v1_ast = myparser.parse(var['destinationWfArg'])
                    v2_ast = myparser.parse(var['sourceWfValue'])
                    if type=="Out":
                        asgn = (ast_to_string(v2_ast,rname),ast_to_string(v1_ast,invokedWorkflowDisplayName))
                    else:
                        asgn = (ast_to_string(v1_ast, invokedWorkflowDisplayName), ast_to_string(v2_ast, rname))
                    assignments.append(asgn)
            # transitions contain a list of transitions
            transitions = []
            for trans in graph[k]['transitions']:
                transition = (trans['value'], trans['destination'])
                # transition = (trans['value'],rname+':'+trans['destination'])
                transitions.append(transition)
            if len(transitions) == 0:
                z3Graph[name] = "(" + guard + "," + 'None' + ", "+str(assignments)+")"
            elif len(transitions) == 1:
                z3Graph[name] = "(" + guard + ", \"" + str(transitions[0][1]) + "\", "+str(assignments)+")"

            elif len(transitions) == 2:
                z3Graph[name] = "(" + guard + "," + "[" + str(transitions[0]) + "," + str(
                    transitions[1]) + "], " +str(assignments)+")"



        print(z3Vars)
        print(z3Graph)
        z3GraphStr = ""
        for (k, v) in z3Graph.items():
            z3GraphStr = z3GraphStr + "\"" + k + "\"" + ": " + v + ",\n"
        z3GraphStr = z3GraphStr[:-2]
        data = "{" + "\"variables\"" + ": " + str(z3Vars) + ",\n" + \
               "\"graph\": { \n" + z3GraphStr + "},\n " + \
               '\"debugColor\": \"' + Colors[(hash(rname) % len(Colors))] + "\",\n " + \
               "\"name\": \"" + rname + "\" }"
        text_file = open(out_path, "w")
        text_file.write(data)
        text_file.close()

        # return z3Graph


def ast_to_string(localast, rname):
    # AST to string - using preorder
    # to change for ternary operations
    if localast.token_type == myparser.TokenType.T_VAR:
        # localstr = 'V['+ localast.value+']'
        localstr = 'V[\'' + rname + ':' + localast.value + '\']'
    else:
        localstr = localast.value
    st = ''
    dr = ''
    if len(localast.children) > 0:

        if len(localast.children[0].children) == 0:
            st = str(ast_to_string(localast.children[0], rname))
        else:
            st = "(" + str(ast_to_string(localast.children[0], rname)) + ")"
        if len(localast.children) == 2:
            if len(localast.children[1].children) == 0:
                dr = str(ast_to_string(localast.children[1], rname))
            else:
                dr = "(" + str(ast_to_string(localast.children[1], rname)) + ")"

    if st == '' and dr == '':
        localstr = localstr
    elif st == '' and dr != '':
        localstr = localstr + ' ' + dr
    elif st != '' and dr == '':
        localstr = localstr + ' ' + st
    elif localast.value in ["And", 'Or']:
        localstr = localstr + '(' + st + ',' + dr + ')'
    else:
        localstr = st + ' ' + localstr + ' ' + dr
    return localstr


def test_parser(inputstring):
    ast = myparser.parse(inputstring)
    graphviz.label(ast)
    graphviz.to_graphviz(ast)


if __name__ == '__main__':
    path = os.path.join('../Models', sys.argv[1])  # "SimpleBankLoan\Pin Check_202105121449166565.json"
    assert os.path.exists(path), "File not found !"
    # rname = sys.argv[2] # Main
    # out_path = path[:-5] + '_parsed.json'
    x = path.rfind("/")
    y = path[:(x - len(path) + 1)]
    assert y != None and len(y) >= 0, "output path not defined"
    out_path = y
    assert os.path.exists(out_path), "output path was not found"
    #print(sys.argv)
    parseGraph(path, out_path)
