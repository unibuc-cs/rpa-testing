
def insertVariables(xamlByLines, maxNumber, variableNumber, flowType):

    for line in xamlByLines:
        if line.__contains__("<Flowchart.Variables>"):
            if flowType == "FlowSwitch":
                index = 1
                while index <= maxNumber:
                    xamlByLines.insert(xamlByLines.index(line) + variableNumber, f"<Variable x:TypeArguments=\"x:String\" Name=\"test_var{variableNumber}\" />")
                    variableNumber += 1
                    index += 1
            elif flowType == "FlowDecision":
                while variableNumber <= maxNumber:
                    xamlByLines.insert(xamlByLines.index(line) + variableNumber, f"<Variable x:TypeArguments=\"x:String\" Name=\"test_var{variableNumber}\" />")
                    variableNumber += 1
                return variableNumber