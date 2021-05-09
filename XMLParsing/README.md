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

## Releases
Releases can be found inside Releases folder. To use the app, one has to use the XMLParsing.exe with the correct arguments.