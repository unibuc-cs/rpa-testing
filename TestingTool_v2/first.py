import json
import csv
import subprocess
import argparse
import os
import sys

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
json_path = "../../../Applications/C#Models/SimpleBankLoanCSharp/outputXamlParser.json"


fuzzer_path = "Main.py"

graph_path = "../../C#Models/SimpleBankLoanCSharp/debugGraph.png"

results_path = "../../C#Models/SimpleBankLoanCSharp/generatedTests.csv"

os.chdir("Applications/Fuzzer/SymbolicFuzzer/")

#call fuzzer
os.system("python "+fuzzer_path+" -workflowsSpecInput "+ json_path+" -outputGraphFile "+graph_path+" -outputResultsFile "+results_path+" -loggingEnabled 1")
