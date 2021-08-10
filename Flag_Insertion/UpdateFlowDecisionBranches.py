from CustomizeAssignActivity import customizeAssignActivity
from ActivityFinder import getIdOfActivity, getReferenceId


def insertActivitiesOnFlowDecisionBranches(xamlByLines, xamlFile):

        # Set the ID number of the next assign activity to be inserted in the XAML file
        activityID = max(list(map(int, getIdOfActivity(xamlFile))))

        # Set the Reference ID of the next activity to be inserted
        referenceID = max(list(map(int, getReferenceId(xamlFile))))

        # Create Branches Dictionary
        dictBranches = {}
        
        number = 0

        flowDecisionIndexes = [x for x in range(len(xamlByLines)) if "<FlowDecision x:" in xamlByLines[x]]
        #print(xamlByLines[360].split("DisplayName=\"")[1].split("\"")[0])

        listOfIndexTrueStart = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "<FlowDecision.True>"]
        
        i = 0
        
        while(i < len(listOfIndexTrueStart)):

                index = listOfIndexTrueStart[i]

                number += 1

                dictBranches[f"test_var{number}"] = "True"

                templateByLines = customizeAssignActivity(referenceID + number, activityID + number, f"test_var{number}", "True")

                templateByLines = templateByLines[::-1]

                for templateLine in templateByLines:
                        xamlByLines.insert(index + 1, templateLine)
                
                listOfIndexTrueStart = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "<FlowDecision.True>"]

                i += 1

        listOfIndexTrueEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowDecision.True>"]
        
        j = 0

        while(j < len(listOfIndexTrueEnd)):

                index = listOfIndexTrueEnd[j]

                xamlByLines.insert(index, "</FlowStep>")
                xamlByLines.insert(index, "</FlowStep.Next>")
                
                listOfIndexTrueEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowDecision.True>"]

                j += 1

        listOfIndexFalseStart = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "<FlowDecision.False>"]
        
        k = 0

        while(k < len(listOfIndexFalseStart)):

                index = listOfIndexFalseStart[k]

                number += 1

                dictBranches[f"test_var{number}"] = "False"

                templateByLines = customizeAssignActivity(referenceID + number, activityID + number, f"test_var{number}", "True")

                templateByLines = templateByLines[::-1]

                for templateLine in templateByLines:
                        xamlByLines.insert(index + 1, templateLine)
                
                listOfIndexFalseStart = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "<FlowDecision.False>"]

                k += 1
        
        listOfIndexFalseEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowDecision.False>"]
        
        l = 0

        while(l < len(listOfIndexFalseEnd)):

                index = listOfIndexFalseEnd[l]

                xamlByLines.insert(index, "</FlowStep>")
                xamlByLines.insert(index, "</FlowStep.Next>")

                listOfIndexFalseEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowDecision.False>"]

                l += 1

        indexFlowchartEnd = xamlByLines.index("</Flowchart>")
        
        for index in range(1, number + 1):
                xamlByLines.insert(indexFlowchartEnd, f"<x:Reference>__ReferenceID{referenceID + index}</x:Reference>")


        xamlFile = '\n'.join(xamlByLines)

        return xamlFile, number, dictBranches
