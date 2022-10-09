from Executor_NodesExec import *
import os
unittestingdataFolder = os.getcwd()

def unitTest1():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(dataStore, externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"myStr",
                                          typeName='Int32',
                                          defaultVal=123, currentContextDataStore=dataStore)
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
    varDecl1 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"myStr", typeName='Int32', defaultVal=123, currentContextDataStore=dataStore)
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
    varDecl1 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"local_test_data",
                                          typeName='DataTable', lazyLoad=False,
                                          defaultPath="unitttestingdata\\pin_mocked_data.csv", currentContextDataStore=dataStore)
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
    varDecl1 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"local_test_data", typeName='DataTable', lazyLoad=True, currentContextDataStore=dataStore)
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
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    varDecl1 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"local_test_data", typeName='DataTable', lazyLoad=True, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(varDecl1, dataStore)

    code_block = r'''
local_test_data = LoadCSV("unitttestingdata\\pin_mocked_data.csv")
PrettyPrint(local_test_data.DataRow.Item(0).Item("Pin:expected_pin"))
PrettyPrint(local_test_data.DataColumn.Item("Pin:expected_pin").Item(1))
PrettyPrint(local_test_data.Rows.Count)
PrettyPrint("Max col: ", local_test_data.Max(column="Pin:expected_pin"))
PrettyPrint("Min col: ", local_test_data.Min(column="Pin:expected_pin"))
PrettyPrint("Sum col: ", local_test_data.Sum(column="Pin:expected_pin"))
local_test_data.UpdateValue(row=1, column="Pin:expected_pin", value=9999)
PrettyPrint("Max col after new add: ", local_test_data.Max("Pin:expected_pin"))
local_test_data.AppendRow(data={"Pin:expected_pin":1010})
local_test_data.SaveToCSV("unitttestingdata\\pin_mocked_data_new.csv")
    '''

    result: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block)

    #if isinstance(result, list) and len(result) > 1:
    #    for codeBlock in result:
    astFuzzerNodeExecutor.executeNode(result, dataStore)



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

# Array tests and access in c# style
def unitTest6():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    annotation = {
            "bounds": 10,
            "min": 0,
            "max": 9999
          }
    varDecl1 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"actual_pin_values",
                                          typeName='Int32[]', annotation=annotation, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(varDecl1, dataStore)

    annotation = {
            "min": 0,
            "max": 9999
    }
    varDecl2 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"local_number_retries",
                                          typeName='Int32', annotation=annotation, defaultValue=0, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(varDecl2, dataStore)

    varDecl3 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"expected_pin",
                                          typeName='Int32', annotation=annotation, defaultValue=9123, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(varDecl3, dataStore)

    # Call a put value function using reference API and call to get ref to a particular index
    code_block1 = "actual_pin_values.SetElementAt(local_number_retries, expected_pin * 10)"
    code_block2 = "PrettyPrint(actual_pin_values.GetElementAt(local_number_retries))"

    result1: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block1)[0]
    astFuzzerNodeExecutor.executeNode(result1, dataStore)

    result2: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block2)[0]
    astFuzzerNodeExecutor.executeNode(result2, dataStore)

    return

def unitTest7():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    # Declare a variable
    annotation = {
            "userInput" : 0, # Put 1 if dictionary values need or influence branching and testing propocess paths !!
            "min": 0,
            "max": 9999
          }

    # Create all dictionaries types and test them

    # int values dict
    #-------------------------
    my_dict_string_Int32 = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"my_dict_string_Int32",
                                          typeName='dictionary_string_Int32', annotation=annotation, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(my_dict_string_Int32, dataStore)

    code_block1_int = "my_dict_string_Int32.setVal(\"key123\", 123)"
    code_block2_int = "PrettyPrint(my_dict_string_Int32.getVal(\"key123\"))"

    res_code_block1_int: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block1_int)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block1_int, dataStore)
    res_code_block2_int: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block2_int)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block2_int, dataStore)
    #-------------------------


    # boolean values dict
    #-------------------------
    my_dict_string_Boolean = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"my_dict_string_Boolean",
                                          typeName='dictionary_string_Boolean', annotation=annotation, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(my_dict_string_Boolean, dataStore)

    code_block1_boolean = "my_dict_string_Boolean.setVal(\"key123\", True)"
    code_block2_boolean = "PrettyPrint(my_dict_string_Boolean.getVal(\"key123\"))"

    res_code_block1_boolean: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block1_boolean)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block1_boolean, dataStore)
    res_code_block2_boolean: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block2_boolean)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block2_boolean, dataStore)

    # string values dict
    #-------------------------
    my_dict_string_String = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"my_dict_string_String",
                                          typeName='dictionary_string_String', annotation=annotation, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(my_dict_string_String, dataStore)

    code_block1_string = "my_dict_string_String.setVal(\"key123\", \"my123string\")"
    code_block2_string = "PrettyPrint(my_dict_string_String.getVal(\"key123\"))"


    res_code_block1_string: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block1_string)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block1_string, dataStore)
    res_code_block2_string: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block2_string)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block2_string, dataStore)


    # float values dict
    #-------------------------
    my_dict_string_Float = ASTFuzzerNode_VariableDecl(varName=ASTFuzzerNode.currentWorkflowNameParsed + ":"+"my_dict_string_Float",
                                          typeName='dictionary_string_Float', annotation=annotation, currentContextDataStore=dataStore)
    astFuzzerNodeExecutor.executeNode(my_dict_string_Float, dataStore)

    code_block1_float = "my_dict_string_Float.setVal(\"key123\", 123.123)"
    code_block2_float = "PrettyPrint(my_dict_string_Float.getVal(\"key123\"))"

    res_code_block1_float: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block1_float)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block1_float, dataStore)
    res_code_block2_float: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_block2_float)[0]
    astFuzzerNodeExecutor.executeNode(res_code_block2_float, dataStore)

    return

def unitTest8():
    # Init the base objects
    dataStore = DataStore()
    externalFunctionsDict = DictionaryOfExternalCalls()
    astFuzzerNodeExecutor = ASTFuzzerNodeExecutor(externalFunctionsDict)
    ourMainWorkflowParser = WorkflowExpressionsParser()

    code_except = "Exception(0, 'msg1')"
    res_code_except: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_except)
    astFuzzerNodeExecutor.executeNode(res_code_except, dataStore)

    code_dateTime_1 = 'PrettyPrint(DateTime("10/9/2022 15:30", "%m/%d/%Y %H:%M").year())'
    res_code_dateTime_1: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_dateTime_1)
    astFuzzerNodeExecutor.executeNode(res_code_dateTime_1, dataStore)

    code_dateTime_2 = 'PrettyPrint(DateTime("10/9/2022 15:30", "%m/%d/%Y %H:%M").month())'
    res_code_dateTime_2: WorkflowCodeBlockParsed = ourMainWorkflowParser.parseModuleCodeBlock(code_dateTime_2)
    astFuzzerNodeExecutor.executeNode(res_code_dateTime_2, dataStore)

if __name__ == '__main__':
    #unitTest1()
    #unitTest2()
    #unitTest3()
    #unitTest4()
    #unitTest5()
    #unitTest6()
    #unitTest7()
    unitTest8()

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
    code_5 = "local_test_data.Rows.Item(0)"
    codeTree2 = ast.parse(code_5)


    #code_5 = "Parse(local_test_data.Rows.Item(0).Item(\"Pin:expected_pin\").ToString())"

    code = code_5
    codeTree = ast.parse(code)
    ourMainWorkflowParser = MainWorkflowParser()
    ourMainWorkflowParser.visit(codeTree)
    result: List[ASTFuzzerNode] = ourMainWorkflowParser.getFinalOutput()
    print(result)

    sys.exit(0)
