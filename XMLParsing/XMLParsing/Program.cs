using System;
using System.Collections.Generic;
using System.IO;
using XMLParsing.Common;
using XMLParsing.Services;
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
                    case ParserCommand.FullGraph:
                        HandleFullGraphCommand(parameterList);
                        break;
                    case ParserCommand.Z3ConditionalGraph:
                        HandleZ3ConditionalGraph(parameterList);
                        break;
                    case ParserCommand.Z3FullGraph:
                        HandleZ3FullGraph(parameterList);
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

            Console.WriteLine("Press any key to exit...");
            Console.ReadLine();

        }

        private static void HandleHelpCommand()
        {
            IOHandler.Instance.WriteHelpInformation();
        }

        private static void HandleFullGraphCommand(List<string> parameters)
        {
            var wf = WorkflowParser.Instance.ParseWorkflow(parameters[0]);
            var serializer = new FullGraphSerializer();
            serializer.SerializeWorkflow(wf, Console.Out);
        }

        private static void HandleZ3ConditionalGraph(List<string> parameters)
        {
            Console.WriteLine("Parsing to z3 conditional graph form");

            var wf = WorkflowParser.Instance.ParseWorkflow(parameters[0]);

            var timeStamp = DateTime.Now.ToString("yyyyMMddHHmmssffff");
            var jsonFilePath = parameters[0].Replace(".xaml", "") + "_" + timeStamp + ".json";

            var serializer = new Z3ConditionalGraphSerializer();
            var textWriter = File.AppendText(jsonFilePath);
            serializer.SerializeWorkflow(wf, textWriter);

            Console.WriteLine("Successfully parsed workflow: " + parameters[0] + ".");
            Console.WriteLine("Output file is: " + jsonFilePath + ".");

            textWriter.Close();
        }

        private static void HandleZ3FullGraph(List<string> parameters)
        {
            Console.WriteLine("Parsing to z3 full graph form");

            var wf = WorkflowParser.Instance.ParseWorkflow(parameters[0]);

            var timeStamp = DateTime.Now.ToString("yyyyMMddHHmmssffff");
            var jsonFilePath = parameters[0].Replace(".xaml", "") + "_" + timeStamp + ".json";

            var serializer = new Z3FullGraphSerializer();
            var textWriter = File.AppendText(jsonFilePath);
            serializer.SerializeWorkflow(wf, textWriter);

            Console.WriteLine("Successfully parsed workflow: " + parameters[0] + ".");
            Console.WriteLine("Output file is: " + jsonFilePath + ".");

            textWriter.Close();
        }
    }
}
