import re

def findNumberOfFlowSwitchBranches(input_text):
        count = 0
        count = sum(1 for _ in re.finditer("<FlowStep x:Key", input_text))
        count += sum(1 for _ in re.finditer("<FlowSwitch.Default>", input_text))
        
        return count