import re
from typing import NewType

line = "randomText__ReferenceID24randomText"

refIdToBeReplaced = list(map(int, re.findall('\d+', line.split("__ReferenceID")[1][:2])))[0]

#print(refIdToBeReplaced)

newPattern = f"__ReferenceID{refIdToBeReplaced + 1}"

line = re.sub(r'__ReferenceID\d+', newPattern, line)
#print(line)

list = ["a", "b", "c", "d"]

list.insert(list.index("c") - 1, "</FlowStep>")
# list.insert(list.index("b") + 1, "</FlowStep.Next>")
#print(list.index("b"))

#res = [x for x in range(len(list)) if list[x] == "b"]
#print(res)
# for elem in list:
#         if elem == "b":
#                 list.insert(list.index(elem) + 1, "<FlowStep.Next>")
#                 list.insert(list.index(elem) + 1, "<FlowStep>")

# print(list)
print(list)