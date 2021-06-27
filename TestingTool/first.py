import json
import csv
import subprocess
import argparse
import os
import sys

sys.path.append('Applications/ExpressionsParser')
import main_parse
sys.path.append('Applications/Fuzzer/SymbolicFuzzer')
import Main

#path to xaml
xaml_path = "../Models/Create Loan Process - With Invoked Pin Check_v2.xaml"

#path to exe
exe_path = "XMLParsing.exe"
os.chdir("Applications/XMLParser/")

#call XMLParser
subprocess.call([exe_path,"/z3ReducedGraph",xaml_path])
os.chdir("../../")

#path to json
json_path = "Applications/Models/outputXamlParser.json"

#call ExpressionsParser 
main_parse.parseGraph(json_path, "Applications/Models") 

fuzzer_path = "Applications/Fuzzer/SymbolicFuzzer/Main.py"

txt_path = "Applications/Models/_tempExpressionParser.txt"

graph_path = "debugGraph.png"

results_path = "Applications/Models/generatedTests.csv"

#call fuzzer
os.system("python "+fuzzer_path+" -testConfigFilePath "+ txt_path+" -outputGraphFile "+graph_path+" -outputResultsFile "+results_path+" -loggingEnabled 1")
