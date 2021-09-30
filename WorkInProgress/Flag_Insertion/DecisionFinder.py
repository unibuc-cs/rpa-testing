import re

def findNumberOfDecisions(input_text):
    count = 0
    count = sum(1 for _ in re.finditer(r'\b%s\b' % re.escape("FlowDecision x"), input_text))
    return count