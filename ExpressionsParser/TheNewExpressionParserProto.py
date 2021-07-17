from Executor_NodesExec import *


def unitTest1():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl("myStr",
                                          'Int32',
                                          defaultVal=123)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Call a simple print function registered externally
    code_block = "PrettyPrint(\"the value of variable is \", myStr)"
    result : WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    return

def unitTest2():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    ourMainWorkflowParser.reset()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl("myStr", 'Int32', defaultVal=123)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Test code: Convert it to string, then to integer, then to float
    code_block = "PrettyPrint(Float.Parse(Int32.Parse(myStr.ToString())))"
    #code_block = "PrettyPrint(myStr.ToString())"
    code_block = ast.parse(code_block)

    ourMainWorkflowParser.visit(code_block)
    result: List[ASTFuzzerNode] = ourMainWorkflowParser.getFinalOutput()

    res = astFuzzerNodeExecutor.executeNode(result)

    pass

def unitTest3():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="local_test_data", typeName='DataTable', lazyLoad=False, path="pin_mocked_data.csv")
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Call a simple print function registered externally
    code_block = "PrettyPrint(Int32.Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString()))"
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    return

def unitTest4():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="local_test_data", typeName='DataTable', lazyLoad=True)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    # Call a simple print function registered externally
    code_block = "local_test_data = LoadCSV(\"pin_mocked_data.csv\")"
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    return

def unitTest5():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName="local_test_data", typeName='DataTable', lazyLoad=True)
    astFuzzerNodeExecutor.executeNode(varDecl1)

    code_block = r'''
local_test_data = LoadCSV("pin_mocked_data.csv")
PrettyPrint(Int32.Parse(local_test_data.Rows.Item(0).Item("Pin:expected_pin").ToString()))
PrettyPrint("Max col: ", local_test_data.Max(column="Pin:expected_pin"))
PrettyPrint("Min col: ", local_test_data.Min(column="Pin:expected_pin"))
PrettyPrint("Sum col: ", local_test_data.Sum(column="Pin:expected_pin"))
local_test_data.UpdateValue(row=1, column="Pin:expected_pin", value=9999)
PrettyPrint("Max col after new add: ", local_test_data.Max("Pin:expected_pin"))
local_test_data.AppendRow(data={"Pin:expected_pin":1010})
local_test_data.SaveToCSV("pin_mocked_data_new.csv")
    '''

    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)



    code = r'''
    print('\n')
    print('hello world')
    '''
    """
    # Call a simple print function registered externally
    code_block = r"local_test_data = LoadCSV(\"pin_mocked_data.csv\")"
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    code_block = 'PrettyPrint("Max col: local_test_data.Max(\"Pin:expected_pin\"))'
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    code_block = 'PrettyPrint(local_test_data.Min(\"Pin:expected_pin\"))'
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)

    code_block = 'PrettyPrint(local_test_data.Sum(\"Pin:expected_pin\"))'
    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)
    astFuzzerNodeExecutor.executeNode(result)
    """

if __name__ == '__main__':
    #unitTest1()
    #unitTest2()
    #unitTest3()
    unitTest4()
    unitTest5()

    sys.exit(0)

    """
    code = "Item(0)" #"Int32.Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"  #'something = a.b.method(foo() + xtime.time(), var=1) + q.y(x.m())' # 'something = a.b.method(foo() + xtime.time(), var=1) + q.y(x.m())'
    tree = ast.parse(code)
    ParseFunctionsVisitor().visit(tree)
    """

    code_1 = "local_number_retries < 3 \n  "
    code_2 = "loan >= 1000 and loan < 100000"
    code_3 = "local_number_retries = local_number_retries + 1"

    code_31 = "obtained_result = loan_type + \" \" + term_type"

    code_4 = "actual_pin_values.ElementAt(local_number_retries) = expected_pin"
    code_5 = "Int32.Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"
    code_5 = "local_test_data.Rows.Item(0).Item2(1)"
    codeTree2 = ast.parse(code_5)


    #code_5 = "Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"

    code = code_5
    codeTree = ast.parse(code)
    ourMainWorkflowParser = MainWorkflowParser()
    ourMainWorkflowParser.visit(codeTree)
    result: List[ASTFuzzerNode] = ourMainWorkflowParser.getFinalOutput()
    print(result)

    sys.exit(0)
