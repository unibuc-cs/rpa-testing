import re

def getReferenceId(input_text):

    listOfReferenceIDs = []

    for match in re.finditer("x:Name=\"__ReferenceID\d+", input_text):
        start = match.start()
        end = match.end()
        listOfReferenceIDs.append(input_text[start:end].split("ID")[1])

    return listOfReferenceIDs

def getIdOfActivity(input_text):

    assignActivitiesIdList = []

    for match in re.finditer("IdRef=\"Assign_\d+", input_text):
        start = match.start()
        end = match.end()
        assignActivitiesIdList.append(input_text[start:end].split("_")[1])

    return assignActivitiesIdList
        