### Flag Insertion ###

This purpose of this project is to insert activities on each branch of the Flow Decision and Flow Switch activities inside UiPath XAML files. This simplies the work of going through all workflows and searching for these branches.

The code:

-> Main.py - the starting point of the process

-> DecisionFinder.py - is responsible for finding the number of flow decisions in the workflow
                     - functions used from this file: findNumberOfDecisions
                                - Input: the xaml workflow in string format
                                - Output: the number of decisions found

-> InsertVariables.py - is responsible for inserting variables inside the xaml file based on the number of flow/switch decisions
                      - functions used from this file: insertVariables
                                - Input: the xaml workflow split by lines, number of flow/switch decisions, the variable count, the flow type 
                                - Output: the variable count (only if the flow type is "FlowDecision")

-> UpdateFlowDecisionBranches.py/UpdateFlowSwitchBranches.py - is responsible for inserting activities on each flow decision/ flow switch branch
                                 - functions used from this file: insertActivitiesOnFlowDecisionBranches
                                        - Input: the xaml file split by lines, the xaml file in string format
                                        - Output: the xaml file in string format, the referenceID count, the dictionary containing the variables and their values (the values are true/false depending on which branch the assignation occurs)
                                 - imports: 
                                        - CustomizeAssignActivity.py: from this file the function customizeAssignActivity is used:
                                                - Input: the reference ID, the activity ID, the variable name, the value of the variable
                                                - Output: the activity template split by lines 
                                        - ActivityFinder.py: from this file the functions getReferenceID:
                                                - Input: xaml file in string format
                                                - Output: the list containing the reference IDs of all the activities
                                                and getIdOfActivity:
                                                - Input: xaml file in string format
                                                - Output: the list containing the activity IDs of all activities

-> FlowSwitchFinder.py - is reponsible for finding the number of flow switch activities in the workflow
                       - Input: xaml file in string format
                       - Output: the number of Flow Switch activities found

-> FlowSwitchBranchFinder.py - is responsible for finding the number of flow switch branches
                             - Input: xaml file in string format
                             - Output: the number Flow Switch branches found

-> CustomizeAssignActivity.py - is reponsible for creating the template of the assign activity (info about the functions found inside this file can be found above)

-> ActivityFinder.py - is responsible for finding the Reference IDs and the Activity IDs (IdRefs) of all activities (more info above)