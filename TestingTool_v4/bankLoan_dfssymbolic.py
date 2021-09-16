import json
import csv
import subprocess
import argparse
import os
import sys
import time

sys.path.append('Applications/Fuzzer/SymbolicFuzzer/')
import Main

#path to xaml
xaml_path = "../C#Models/SimpleBankLoanCSharp/Main.xaml"

#path to exe
exe_path = "XMLParsing.exe"
os.chdir("Applications/XMLParser/")

#call XMLParser
subprocess.call([exe_path,"/z3ReducedGraph",xaml_path])
os.chdir("../../")

#path to json
json_path = "../../C#Models/SimpleBankLoanCSharp/"
json_name = "outputXamlParser.json"
print("Current Working Directory " , os.getcwd())
print("JSON PATH",json_path)

fuzzer_path = "Main.py"

graph_path = "debugGraph.png"

results_path = "generatedTests"

os.chdir("Applications/Fuzzer/SymbolicFuzzer/")
print("Current Working Directory " , os.getcwd())
start_time = time.time()
#call fuzzer
os.system("python "+fuzzer_path+" -modelBasePath "+json_path+" -workflowsSpecInput "+ json_name+" -solverStrategy STRATEGY_DFS "+" -debug_outputGraphFile "+graph_path+" -outputTests_PrefixFile "+results_path+" -outputTests_MaxTestPerFile 5 -debug_tests_fullPaths 0 -debug_consoleOutput 0 -debug_tests_fullVariablesContent 0")
execution_time = time.time() - start_time
logs_path = "../../C#Models/SimpleBankLoanCSharp/executionLogs.txt"
# open the file in the write mode
f= open(logs_path,"a+")
f.write("Execution time fuzzer DFS symbolic %f seconds\n" % execution_time)
f.close()
  