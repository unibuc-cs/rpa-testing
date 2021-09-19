import json
import csv
import subprocess
import argparse
import os
import sys
import time


sys.path.append('Applications/Fuzzer/SymbolicFuzzer/')
import Main

print("Current Working Directory " , os.getcwd())

#get user input from json
with open ('userInput.json','r') as f:
    userInput_dict = json.load(f)
print (str(userInput_dict))

xaml_path = userInput_dict['xamlPath']
modelBasePath = userInput_dict['modelBasePath']
solverStrategy = userInput_dict['solverStrategy']
outputTests_MaxTestPerFile = userInput_dict['outputTests_MaxTestPerFile']
debug_tests_fullPaths = userInput_dict['debug_tests_fullPaths']
debug_ConsoleOutput = userInput_dict['debug_ConsoleOutput']
debug_tests_fullVariablesContent = userInput_dict['debug_tests_fullVariablesContent']
seedsFile = userInput_dict['seedsFile']
numRandomGeneratedSeeds = userInput_dict['numRandomGeneratedSeeds']

print("Current Working Directory " , os.getcwd())
#path to XMLParser exe
exe_path = "XMLParsing.exe"
os.chdir("Applications/XMLParser/")

#call XMLParser
subprocess.call([exe_path,"/z3ReducedGraph",xaml_path])
os.chdir("../../")

json_name = "outputXamlParser.json"
print("Current Working Directory " , os.getcwd())

fuzzer_path = "Main.py"

graph_path = "debugGraph.png"

results_path = "generatedTests"

os.chdir("Applications/Fuzzer/SymbolicFuzzer/")
print("Current Working Directory " , os.getcwd())
start_time = time.time()

#call fuzzer
os.system("python "+fuzzer_path+" -modelBasePath "+modelBasePath+" -workflowsSpecInput "+ json_name+" -solverStrategy "+solverStrategy+" -debug_outputGraphFile "+graph_path+" -outputTests_PrefixFile "+results_path+" -outputTests_MaxTestPerFile "+str(outputTests_MaxTestPerFile)+" -debug_tests_fullPaths "+str(debug_tests_fullPaths)+" -debug_consoleOutput "+str(debug_ConsoleOutput)+" -debug_tests_fullVariablesContent "+str(debug_tests_fullVariablesContent))
execution_time = time.time() - start_time
logs_path = modelBasePath+"executionLogs.txt"
# open the file in the write mode
f= open(logs_path,"a+")
f.write("Fuzzer strategy ---- %s, Execution time ----%f seconds\n" % (solverStrategy,execution_time))
f.close()
