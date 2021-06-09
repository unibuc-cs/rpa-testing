using System;
using System.Collections.Generic;
using XMLParsing.Utils;

namespace XMLParsing.Services
{
    class IOHandler
    {

        private static readonly Lazy<IOHandler> LazyInstance = new Lazy<IOHandler>(() => new IOHandler());

        public enum ParserCommand
        {
            Help,
            Z3ConditionalGraph,
            Z3FullGraph,
            Z3ReducedGraph
        }

        private static IDictionary<string, ParserCommand> _stringToParserCommand = new Dictionary<string, ParserCommand>() {
            { "/help", ParserCommand.Help },
            { "/z3ConditionalGraph", ParserCommand.Z3ConditionalGraph  },
            { "/z3FullGraph", ParserCommand.Z3FullGraph },
            { "/z3ReducedGraph", ParserCommand.Z3ReducedGraph },
        };

        private static IDictionary<ParserCommand, string> _descriptions = new Dictionary<ParserCommand, string>() {
            { ParserCommand.Help, "Gives a description of the available parser commands." },
            { ParserCommand.Z3ConditionalGraph, "Parses the workflow file given by argument and outputs the structure in a " +
                                                "Z3 friendly format. Reduces the graph to conditionals." },
            { ParserCommand.Z3FullGraph, "Parses the workflow file given by argument and outputs the structure in a " +
                                                "Z3 friendly format. Outputs the whole graph." },
            { ParserCommand.Z3ReducedGraph, "Parses the workflow file given by argument and outputs the structure in a " +
                                                "Z3 friendly format. Outputs only relevant nodes of the graph." },
        };

        // TODO: Handle context variables for Z3ConditionalGraph 
        private static IDictionary<ParserCommand, string[]> _additionalParameters = new Dictionary<ParserCommand, string[]>() {
            { ParserCommand.Help, new string[] {} },
            { ParserCommand.Z3ConditionalGraph, new string[] { "<workflow-file-path>" } },
            { ParserCommand.Z3FullGraph, new string[] { "<workflow-file-path>" } },
            { ParserCommand.Z3ReducedGraph, new string[] { "<workflow-file-path>" } },
        };

        private IOHandler()
        {
        }

        public static IOHandler Instance
        {
            get
            {
                return LazyInstance.Value;
            }
        }

        public Tuple<ParserCommand, List<string>> ParseInput(string[] args)
        {
            if (args.Length == 0 || args[0].Length < 2 || ! args[0].StartsWith("/"))
            {
                throw new XamlParserException("Command is not valid.");
            }

            if(!_stringToParserCommand.ContainsKey(args[0]))
            {
                throw new XamlParserException("Command is not recognized. Use /help for getting more information");
            }

            ParserCommand parserCommand = _stringToParserCommand[args[0]];
            if(args.Length - 1 != _additionalParameters[parserCommand].Length)
            {
                throw new XamlParserException("Command expects a different number of parameters. Use /help for getting more information");
            }

            List<string> parameters = new List<string>() { };
            for(int i = 1; i < args.Length; i++)
            {
                parameters.Add(args[i]);
            }

            return new Tuple<ParserCommand, List<string>>(parserCommand, parameters);
        }

        public void WriteHelpInformation()
        {
            Console.WriteLine("XmlParser available commands: ");
            foreach(var textCommand in _stringToParserCommand.Keys)
            {
                Console.Write(textCommand + " ");
                ParserCommand parserCommand = _stringToParserCommand[textCommand];
                string[] parameters = _additionalParameters[parserCommand];
                for(int i = 0; i < parameters.Length; i++)
                {
                    Console.Write(parameters[i] + " ");
                }
                Console.Write("\n");
                Console.Write("\t" + _descriptions[parserCommand] + "\n");
            }
        }

    }
}
