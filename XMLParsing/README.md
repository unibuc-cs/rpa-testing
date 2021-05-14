# XML Parsing

## What is it?
XML Parsing is a project designed to parse workflow from .xaml format to any desired format.

## How to use?
The application can be used from command line.
Available commands are:
\/**help**
        Gives a description of the available parser commands.
\/**fullGraph** <worflow-file-path>
        Parses** the workflow file given by argument and outputs the structure in the console.
\/**z3ConditionalGraph** <workflow-file-path>
        Parses the workflow file given by argument and outputs the structure in a Z3 friendly format. Reduces the graph to conditionals.
\/**z3FullGraph** <workflow-file-path>
        Parses the workflow file given by argument and outputs the structure in a Z3 friendly format. Outputs the whole graph.
        
The commands that imply outputing in a z3 friendly format are outputing the data in a .json file, in the same place where the .xaml file is.
E.g.: Xaml file is `C:\this-is-a-complex-wf.xaml`, then the following json file will be generated: `C:\this-is-a-complex-wf-<timestamp>.json`.

## Releases
Releases can be found inside Releases folder. (https://github.com/unibuc-cs/rpa-testing/tree/master/XMLParsing/Releases)
To use the app, one has to use the XMLParsing.exe with the correct arguments.
