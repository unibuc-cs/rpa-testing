import json
import csv
import subprocess
import argparse
import os
import sys

sys.path.append('Applications/Fuzzer/SymbolicFuzzer/')
import Main

#path to xaml
xaml_path = "../C#Models/ContractModel/Main.xaml"

#path to exe
exe_path = "XMLParsing.exe"
os.chdir("Applications/XMLParser/")

#call XMLParser
subprocess.call([exe_path,"/z3ReducedGraph",xaml_path])
os.chdir("../../")

#path to json
json_path = "../../C#Models/ContractModel/"
json_name = "outputXamlParser.json"
print("Current Working Directory " , os.getcwd())
print("JSON PATH",json_path)

fuzzer_path = "Main.py"

graph_path = "debugGraph.png"
#"../../C#Models/SimpleBankLoanCSharp/

results_path = "generatedTests.csv"

os.chdir("Applications/Fuzzer/SymbolicFuzzer/")
print("Current Working Directory " , os.getcwd())
#call fuzzer
os.system("python "+fuzzer_path+" -modelBasePath "+json_path+" -workflowsSpecInput "+ json_name+" -outputGraphFile "+graph_path+" -outputResultsFile "+results_path+" -loggingEnabled 1"+" -solverStrategy STRATEGY_DFS")
