using System;
using System.Collections.Generic;
using System.IO;
using XMLParsing.Common;
using XMLParsing.Services;
using XMLParsing.Services.Reducers;
using XMLParsing.Services.Serializers;
using XMLParsing.Utils;
using static XMLParsing.Services.IOHandler;

namespace XMLParsing
{
    class Program
    {


        /*
            Program arguments are expected to be:
            1. /command where command is one of the commands specified inside IOHandler::Command
            2. Additional parameters depending on the command requested
         */
        static void Main(string[] args)
        {
            // string path = @"..\..\..\..\Models\SimpleBankLoan\Create Loan Process.xaml";
            try
            {
                var ( parserCommand, parameterList ) = IOHandler.Instance.ParseInput(args);
                switch(parserCommand)
                {
                    case ParserCommand.Help:
                        HandleHelpCommand();
                        break;
                    case ParserCommand.Z3ConditionalGraph:
                        HandleZ3ConditionalGraph(parameterList);
                        break;
                    case ParserCommand.Z3FullGraph:
                        HandleZ3FullGraph(parameterList);
                        break;
                    case ParserCommand.Z3ReducedGraph:
                        HandleZ3ReducedGraph(parameterList);
                        break;
                }
            }
            catch (XamlParserException ex)
            {
                Console.WriteLine("Parser exception: " + ex.Message);
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.Message);
                Console.WriteLine(ex.StackTrace);
            }

             // Console.WriteLine("Press any key to exit...");
             // Console.ReadLine();

        }

        private static void HandleHelpCommand()
        {
            IOHandler.Instance.WriteHelpInformation();
        }

        private static void HandleZ3ConditionalGraph(List<string> parameters)
        {
            Console.WriteLine("Parsing to z3 conditional graph form");

            var graph = WorkflowParser.Instance.ParseGraph(parameters[0]);

            var timeStamp = DateTime.Now.ToString("yyyyMMddHHmmssffff");
            var jsonFilePath = parameters[0].Replace(".xaml", "") + "_" + timeStamp + ".json";

            var serializer = new Z3ConditionalGraphSerializer();
            var textWriter = File.AppendText(jsonFilePath);
            serializer.SerializeWorkflow(graph, textWriter);

            Console.WriteLine("Successfully parsed workflow: " + parameters[0] + ".");
            Console.WriteLine("Output file is: " + jsonFilePath + ".");

            textWriter.Close();
        }

        private static void HandleZ3FullGraph(List<string> parameters)
        {
            Console.WriteLine("Parsing to z3 full graph form");

            var graph = WorkflowParser.Instance.ParseGraph(parameters[0]);

            var timeStamp = DateTime.Now.ToString("yyyyMMddHHmmssffff");
            var jsonFilePath = parameters[0].Replace(".xaml", "") + "_" + timeStamp + ".json";
            var workflowFilePath = parameters[0];
            SerializeZ3Graph(jsonFilePath, workflowFilePath, graph);

        }

        private static void HandleZ3ReducedGraph(List<string> parameters)
        {
            Console.WriteLine("Parsing to z3 reduced graph form");

            var graph = WorkflowParser.Instance.ParseGraph(parameters[0]);

            var wokflowReducer = new Z3RelevantWorkflowReducer();
            wokflowReducer.ReduceWorkflow(graph);

            var timeStamp = DateTime.Now.ToString("yyyyMMddHHmmssffff");
            var jsonFilePath = parameters[0].Replace(".xaml", "") + "_" + timeStamp + ".json";
            var workflowFilePath = parameters[0];
            SerializeZ3Graph(jsonFilePath, workflowFilePath, graph);
        }

        private static void SerializeZ3Graph(string jsonFilePath, string workflowFilePath, Graph wf)
        {
            var serializer = new Z3FullGraphSerializer();
            var textWriter = File.AppendText(jsonFilePath);
            serializer.SerializeWorkflow(wf, textWriter);

            Console.WriteLine("Successfully parsed workflow: " + workflowFilePath + ".");
            Console.WriteLine("Output file is: " + jsonFilePath + ".");
            textWriter.Close();

            string destinationFileName = "outputXamlParser.json";
            CopyFileContent(jsonFilePath, destinationFileName);
            Console.WriteLine("Copied the content to " + destinationFileName);
        }

        private static void CopyFileContent(string sourceFile, string destinationFile)
        {
            destinationFile = new FileInfo(sourceFile).Directory.FullName + "\\" + destinationFile;
            File.Copy(sourceFile, destinationFile, true);
        }
    }
}
