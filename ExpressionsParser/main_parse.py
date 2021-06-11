import myparser
import graphviz
import json
import sys
import pickle
import os

OUTPUT_FILE_NAME = "_tempExpressionParser.txt" # The name output obtained after running the script on the given input

DataTypes = {
    'Int32': 'Int',
    'String': 'String',
    'Boolean': 'Bool',
    "Double": 'Real',
    "Decimal": 'Real'
}

AllDebugColors = ["red", "blue", "yellow", "green", "violet", "orange"]
NumDebugColors = len(AllDebugColors)
def getDebugColorByName(name : str) -> str:
    return AllDebugColors[(hash(name) % NumDebugColors)]


def parseGraph(path, basePath):
    with open(path) as json_file:
        dataAll = json.load(json_file)

        workflowsDataSpec = dataAll['workflows']
        graph = dataAll['graph']
        startNode = dataAll['startNode']
        startGraph = startNode.split(":")
        assert len(startGraph) > 0
        mainWorkflowName = startGraph[0]

        z3Vars = {}
        z3Graph = {}
        debugColors = {}

        # Create debug colors and append to the variables dictionary each individual workflow used
        for workflowData in workflowsDataSpec:
            variables = workflowData['variables']
            graphName = workflowData['displayName']
            debugColors[graphName] = getDebugColorByName(graphName)

            for v in variables:
                # z3Vars[v] = DataTypes[variables[v]]
                z3Vars[graphName + ':' + v] = DataTypes[variables[v]]
                # z3Vars['Main:'+v] = DataTypes[variables[v]]

        # Where to write the output
        out_path = os.path.join(basePath, OUTPUT_FILE_NAME) #mainWorkflowName)

        # Parse the entire graph and save it in a file
        for nodeFullName, nodeData in graph.items():
            # DEBUG
            """
            if "Assign_20" in k:
                a = 3
                a += 1
            """

            nodeFullNameSplit = nodeFullName.split(":")
            assert len(nodeFullNameSplit) ==2, f"Node content is {nodeFullNameSplit}. Expecting format namespace:nodeName"
            parentGraphName = nodeFullNameSplit[0]
            nodeName = nodeFullNameSplit[1]


            # the guard will contain the expression parsed using myparser
            if nodeData['expression'] == '':
                guard = 'None'
            else:
                ast = myparser.parse(nodeData['expression'])
                guard = "\"" + ast_to_string(ast, parentGraphName) + "\""

            # assigments
            assign_list = nodeData.get("variableAssignments")
            assignments = []
            if assign_list:
               assignment_var = assign_list['to']
               assignment_exp = assign_list['value']
               ast_v = myparser.parse(assignment_var)
               ast_e = myparser.parse(assignment_exp)
               if ast_e.token_type == myparser.TokenType.T_VAR:
                    ast_e_str = ast_to_string(ast_e, parentGraphName)
               else:
                   ast_e_str =  ast_to_string(ast_e, parentGraphName)
               assignments.append((ast_to_string(ast_v, parentGraphName), ast_e_str))

            #invoked wf args
            invokedWorkflow = nodeData.get("invokedWorkflow")
            if invokedWorkflow:
                variableMappings = nodeData["variableMappings"]
                invokedWorkflowDisplayName = nodeData.get("invokedWorkflowDisplayName")
                print(invokedWorkflowDisplayName)
                if invokedWorkflowDisplayName == None:
                    invokedWorkflowDisplayName="Wf2"
                for var in variableMappings:
                    type = var['argumentType']
                    v1_ast = myparser.parse(var['destinationWfArg'])
                    v2_ast = myparser.parse(var['sourceWfValue'])
                    if type=="Out":
                        asgn = (ast_to_string(v2_ast,parentGraphName),ast_to_string(v1_ast,invokedWorkflowDisplayName))
                    else:
                        asgn = (ast_to_string(v1_ast, invokedWorkflowDisplayName), ast_to_string(v2_ast, parentGraphName))
                    assignments.append(asgn)
            # transitions contain a list of transitions
            transitions = []
            for trans in nodeData['transitions']:
                transition = (trans['value'], trans['destination'])
                # transition = (trans['value'],rname+':'+trans['destination'])
                transitions.append(transition)
            if len(transitions) == 0:
                z3Graph[nodeFullName] = "(" + guard + "," + 'None' + ", "+str(assignments)+")"
            elif len(transitions) == 1:
                z3Graph[nodeFullName] = "(" + guard + ", \"" + str(transitions[0][1]) + "\", "+str(assignments)+")"

            elif len(transitions) == 2:
                z3Graph[nodeFullName] = "(" + guard + "," + "[" + str(transitions[0]) + "," + str(
                    transitions[1]) + "], " +str(assignments)+")"


        print(z3Vars)
        print(z3Graph)
        z3GraphStr = ""
        for (k, v) in z3Graph.items():
            z3GraphStr = z3GraphStr + "\"" + k + "\"" + ": " + v + ",\n"
        z3GraphStr = z3GraphStr[:-2]
        data = "{" + "\"variables\"" + ": " + str(z3Vars) + ",\n" + \
               "\"graph\": { \n" + z3GraphStr + "},\n " + \
               '\"debugColors\": \"' + str(debugColors) + "\",\n " + \
                "\"startNode\": " + "\"" + startNode + "\",\n " + \
               "\"mainWorkflowName\": \"" + mainWorkflowName + "\" }" + "\n"

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
