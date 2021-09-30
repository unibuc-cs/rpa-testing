from DecisionFinder import findNumberOfDecisions
from FlowSwitchFinder import findNumberOfSwitchFlows
from FlowSwitchBranchFinder import findNumberOfFlowSwitchBranches
from InsertVariables import insertVariables
from UpdateFlowDecisionBranches import insertActivitiesOnFlowDecisionBranches
from UpdateFlowSwitchBranches import insertActivitiesOnFlowSwitchBranches

# The Input Path
path = "Flag_Insertion_Robot/testing.xaml"

# The Output Path
outputPath = "Flag_Insertion_Robot/Main2.xaml"

# Initialize Flow Decision Branches Dictionary
dictFlowDecisionBranches = {}

# Initialize Flow Switch Branches Dictionary
dictFlowSwitchBranches = {}

# Initialize the number of variables to be inserted
numberOfVariables = 1

# Initialize the number of inserted activities
numberOfActivities = 0

# Read the xaml file
with open(path, 'r') as f:
    xamlFile = f.read()

# Find number of decisions
numberOfFlowDecisions = findNumberOfDecisions(xamlFile)
 
if numberOfFlowDecisions > 0:

    # Split by lines
    xamlByLines = [i.strip() for i in xamlFile.splitlines()]

    # Insert variables
    numberOfVariables = insertVariables(xamlByLines, 2 * numberOfFlowDecisions, numberOfVariables, "FlowDecision")

    # Assemble back the XAML File
    xamlFile = '\n'.join(xamlByLines)

    # Insert the Assign Activities
    xamlFile, numberOfActivities, dictFlowDecisionBranches = insertActivitiesOnFlowDecisionBranches(xamlByLines, xamlFile)

# Find number of switch flows
numberOfFlowSwitches = findNumberOfSwitchFlows(xamlFile)

# Find number of switch flow branches
numberOfFlowSwitchBranches = findNumberOfFlowSwitchBranches(xamlFile)

if numberOfFlowSwitches > 0:

    # Split by lines
    xamlByLines = [i.strip() for i in xamlFile.splitlines()]

    # Insert variables
    _ = insertVariables(xamlByLines, numberOfFlowSwitchBranches, numberOfVariables, "FlowSwitch")

    # Assemble back the XAML File
    xamlFile = '\n'.join(xamlByLines)

    # Insert the Assign Activities
    xamlFile, dictFlowSwitchBranches = insertActivitiesOnFlowSwitchBranches(xamlByLines, xamlFile, numberOfActivities)

# Output the modified Main.xaml file
with open(outputPath, "w") as f:
    f.write(xamlFile)

# Output the dictionaries
pathToFlowDecisionDict = "Output/flow_decision_dictionary.txt"
pathToFlowSwitchDict =  "Output/flow_switch_dictionary.txt"

with open(pathToFlowDecisionDict, "w") as f:
    f.write("variable,value\n")
    for key, value in dictFlowDecisionBranches.items():
        f.write(key + "," + value + "\n")

with open(pathToFlowSwitchDict, "w") as f:
    f.write("variable,value\n")
    for key, value in dictFlowSwitchBranches.items():
        f.write(key + "," + value + "\n")


print(dictFlowDecisionBranches)
print(dictFlowSwitchBranches)