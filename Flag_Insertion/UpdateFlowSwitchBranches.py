from CustomizeAssignActivity import customizeAssignActivity
from ActivityFinder import getIdOfActivity, getReferenceId


def insertActivitiesOnFlowSwitchBranches(xamlByLines, xamlFile, numberOfActivities):

        # Set the ID number of the next assign activity to be inserted in the XAML file
        activityID = max(list(map(int, getIdOfActivity(xamlFile))))

        # Set the Reference ID of the next activity to be inserted
        referenceID = max(list(map(int, getReferenceId(xamlFile))))

        # Create Branch Dictionary
        dictBranches = {}
        
        initialNumber = numberOfActivities + 1

        flowSwitchIndexes = [x for x in range(len(xamlByLines)) if "<FlowStep x:Key" in xamlByLines[x]]
        #print(xamlByLines[360].split("DisplayName=\"")[1].split("\"")[0])
        print(flowSwitchIndexes)
        
        listOfIndexDefaultStart = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "<FlowSwitch.Default>"]
        
        if len(listOfIndexDefaultStart) > 0:

                i = 0
                
                while(i < len(listOfIndexDefaultStart)):
                        
                        index = listOfIndexDefaultStart[i]

                        numberOfActivities += 1

                        dictBranches[f"test_var{numberOfActivities}"] = "Default"

                        templateByLines = customizeAssignActivity(referenceID + numberOfActivities,
                                                                activityID + numberOfActivities,
                                                                f"test_var{numberOfActivities}",
                                                                "Default")

                        templateByLines = templateByLines[::-1]

                        for templateLine in templateByLines:
                                xamlByLines.insert(index + 1, templateLine)
                        
                        listOfIndexDefaultStart = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "<FlowSwitch.Default>"]

                        i += 1

                listOfIndexDefaultEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowSwitch.Default>"]
                
                j = 0

                while(j < len(listOfIndexDefaultEnd)):

                        index = listOfIndexDefaultEnd[j]

                        xamlByLines.insert(index, "</FlowStep>")
                        xamlByLines.insert(index, "</FlowStep.Next>")
                        
                        listOfIndexDefaultEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowSwitch.Default>"]

                        j += 1
        
        listOfIndexKeyStart = [x for x in range(len(xamlByLines)) if "<FlowStep x:Key=" in xamlByLines[x]]
        
        k = 0
        
        while(k < len(listOfIndexKeyStart)):
                
                if k > 0:
                        index = listOfIndexKeyStart[k]
                        xamlByLines.insert(index, "</FlowStep>")
                        xamlByLines.insert(index, "</FlowStep.Next>")
                        listOfIndexKeyStart = [x for x in range(len(xamlByLines)) if "<FlowStep x:Key=" in xamlByLines[x]]

                index = listOfIndexKeyStart[k]

                numberOfActivities += 1

                keyName = xamlByLines[index].split("x:Key=\"")[1].split("\"")[0]

                dictBranches[f"test_var{numberOfActivities}"] = keyName

                templateByLines = customizeAssignActivity(referenceID + numberOfActivities,
                                                        activityID + numberOfActivities,
                                                        f"test_var{numberOfActivities}",
                                                        keyName)

                referenceLine = templateByLines[0]
                templateByLines.append(referenceLine)
                templateByLines = templateByLines[1:]
                templateByLines = templateByLines[::-1]

                for templateLine in templateByLines:
                        xamlByLines.insert(index + 1, templateLine)
                
                listOfIndexKeyStart = [x for x in range(len(xamlByLines)) if "<FlowStep x:Key=" in xamlByLines[x]]

                k += 1
        
        listOfIndexFlowSwitchEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowSwitch>"]
        
        l = 0

        while(l < len(listOfIndexFlowSwitchEnd)):

                index = listOfIndexFlowSwitchEnd[l]

                xamlByLines.insert(index, "</FlowStep>")
                xamlByLines.insert(index, "</FlowStep.Next>")
                
                listOfIndexFlowSwitchEnd = [x for x in range(len(xamlByLines)) if xamlByLines[x] == "</FlowSwitch>"]

                l += 1

        indexFlowchartEnd = xamlByLines.index("</Flowchart>")
        
        for index in range(initialNumber, numberOfActivities + 1):
                xamlByLines.insert(indexFlowchartEnd, f"<x:Reference>__ReferenceID{referenceID + index}</x:Reference>")

        xamlFile = '\n'.join(xamlByLines)

        return xamlFile, dictBranches
