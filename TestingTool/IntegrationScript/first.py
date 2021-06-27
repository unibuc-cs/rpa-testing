import json
import csv
import subprocess
import argparse

import os

import sys

#from Applications.ExpressionsParser import main_parse
sys.path.append('Applications/ExpressionsParser')
import main_parse
sys.path.append('Applications/Fuzzer/SymbolicFuzzer')
import Main

#from Applications.Fuzzer.SymbolicFuzzer import Main

#path to xaml
#source = os.path.dirname(__file__)
#parent = os.path.join(source, '../Models\\SimpleBankLoan')
#xaml_path = os.path.join(parent, 'Create Loan Process - With Invoked PinCheck_v1.xaml')

xaml_path = "Applications\\Models\\Create Loan Process - With Invoked Pin Check_v2.xaml"

#path to exe
#source = os.path.dirname(__file__)
#parent = os.path.join(source, '../XMLParsing\\Releases\\0.6.0')
#exe_path = os.path.join(parent, 'XMLParsing.exe')
exe_path = "Applications\\XMLParser\\XMLParsing.exe"
#call XMLParser
subprocess.call([exe_path,"/z3ReducedGraph",xaml_path])

#path to json
#source = os.path.dirname(__file__)
#parent = os.path.join(source, '../Models\\SimpleBankLoan')
#json_path = os.path.join(parent, 'outputXamlParser.json')
json_path = "Applications\\Models\\outputXamlParser.json"
#call ExpressionsParser - inca nu se genereaza ca output un txt de catre ExpressionsParser; 
main_parse.parseGraph(json_path,"Applications\\Models") 

#source = os.path.dirname(__file__)
#parent = os.path.join(source, '../Fuzzer\\SymbolicFuzzer')
#fuzzer_path = os.path.join(parent, 'Main.py')
fuzzer_path = "Applications\\Fuzzer\\SymbolicFuzzer\\Main.py"
#txt_path = os.path.join(parent,'dummy_TestSpec.txt')
txt_path = "Applications\\Models\\_tempExpressionParser.txt"

#source = os.path.dirname(__file__)
#parent = os.path.join(source, '../Models\\SimpleBankLoan')
#graph_path = os.path.join(parent, 'debugGraph.png')
graph_path = "Applications\\Models\\debugGraph.png"

#source = os.path.dirname(__file__)
#parent = os.path.join(source, '../Models\\SimpleBankLoan')
#results_path = os.path.join(parent, 'generatedTests.csv')
results_path = "Applications\\Models\\generatedTests.csv"

os.system("python "+fuzzer_path+" -testConfigFilePath "+ txt_path+" -outputGraphFile "+graph_path+" -outputResultsFile "+results_path+" -loggingEnabled 1")


#subprocess.call([fuzzer_path,"-testConfigFilePath "+txt_path,"-outputGraphFile "+graph_path, "-outputResultsFile "+results_path, "-loggingEnabled 1"],shell=True)
#subprocess.call(["XMLParsing\\Releases\\0.6.0\\XMLParsing.exe","/z3FullGraph","Models\\SimpleBankLoan\\Create Loan Process - With Invoked PinCheck_v1.xaml"])
#path to json generated after calling xaml parser
#jsonFilePath = '../ModelsSimpleBankLoan\\outputXamlParser.json'

#call expression parser
#main_parse.parseGraph("../Models\\SimpleBankLoan\\outputXamlParser.json","Main")



#os.system("python ../Fuzzer\\SymbolicFuzzer\\Main.py -testConfigFilePath ../Fuzzer\\SymbolicFuzzer\\dummy_TestSpec.txt -outputGraphFile ../Models\\SimpleBankLoan\\debugGraph.png -outputResultsFile ../Models\\SimpleBankLoan\\generatedtests.csv -loggingEnabled 1")







#print(textFile)    
#subprocess.call(["C:\\GithubPhD\\rpa-testing\\Fuzzer\\SymbolicFuzzer\\Main.py","-testConfigFilePath C:\\GithubPhD\\rpa-testing\\Fuzzer\\SymbolicFuzzer\\dummy_TestSpec.txt","-outputGraphFile debugGraph.png", "-outputResultsFile generatedests.csv", "-loggingEnabled 1"],shell=True)
#parser = argparse.ArgumentParser(description='Fuzzer process')
#parser.add_argument('-testConfigFilePath', type=str, help='Path to the config file', required=True)
#parser.add_argument('-outputGraphFile', type=str, default="debugGraph.png", help='Path to the output debug graph file', required=True)
#parser.add_argument('-loggingEnabled', type=int, default=1, help='Verbose everything ?', required=True)
#parser.add_argument('-outputResultsFile', type=str, default="generatedests.csv", help='Path to write the output CSV file', required=True)
#args = parser.parse_args(['-testConfigFilePath=C:\\GithubPhD\\rpa-testing\\Fuzzer\\SymbolicFuzzer\\dummy_TestSpec.txt', '-outputGraphFile=C:\\GithubPhD\\rpa-testing\\Fuzzer\\SymbolicFuzzer\\debugGraph.png', '-outputResultsFile=C:\\GithubPhD\\rpa-testing\\Fuzzer\\SymbolicFuzzer\\generatedests.csv', '-loggingEnabled=1'])
#args.loggingEnabled = False if args.loggingEnabled == 0 else True
#Main.runTest(args)
#third.metoda3(textFile)

#with open('third_response.csv', newline='') as csvfile:
 #   csvReader = csv.reader(csvfile, delimiter=' ', quotechar='|')

  #  for row in csvReader:

   #     print(', '.join(row))
    