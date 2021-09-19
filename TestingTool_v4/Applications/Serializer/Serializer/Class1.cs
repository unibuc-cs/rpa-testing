using System.Activities;
using System.ComponentModel;
using Newtonsoft.Json.Linq;
using System.IO;

namespace Serializer
{
    public class RequiredDataIntoJson : CodeActivity
    {
        [Category("Input")]
        [RequiredArgument]
        public InArgument<string> ModelBasePath { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<string> SolverStrategy { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<int> OutputTests_MaxTestPerFile { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<int> Debug_tests_fullPaths { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<int>  Debug_consoleOutput { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<int> Debug_tests_fullVariablesContent { get; set; }

        [Category("Input")]
        public InArgument<string> SeedsFile { get; set; }

        [Category("Input")]
        public InArgument<int> NumRandomGeneratedSeeds { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<string> OutputJsonPath { get; set; }

        [Category("Input")]
        [RequiredArgument]
        public InArgument<string> XamlPath { get; set; }

        protected override void Execute(CodeActivityContext context)
        {
            var modelBasePath = ModelBasePath.Get(context);
            var solverStrategy = SolverStrategy.Get(context);
            var outputTests_MaxTestPerFile = OutputTests_MaxTestPerFile.Get(context);
            var debug_tests_fullPaths = Debug_tests_fullPaths.Get(context);
            var debug_ConsoleOutput = Debug_consoleOutput.Get(context);
            var debug_tests_fullVariablesContent = Debug_tests_fullVariablesContent.Get(context);
            var seedsFile = SeedsFile.Get(context);
            var numRandomGeneratedSeeds = NumRandomGeneratedSeeds.Get(context);
            var outputJsonPath = OutputJsonPath.Get(context);
            var xamlPath = XamlPath.Get(context);

            JObject FuzzerInput = new JObject(
                new JProperty("xamlPath", xamlPath),
                new JProperty("modelBasePath", modelBasePath),
                new JProperty("solverStrategy", solverStrategy),
                new JProperty("outputTests_MaxTestPerFile", outputTests_MaxTestPerFile),
                new JProperty("debug_tests_fullPaths", debug_tests_fullPaths),
                new JProperty("debug_ConsoleOutput", debug_ConsoleOutput),
                new JProperty("debug_tests_fullVariablesContent", debug_tests_fullVariablesContent),
                new JProperty("seedsFile", seedsFile),
                new JProperty("numRandomGeneratedSeeds", numRandomGeneratedSeeds)
                );
            File.WriteAllText(@outputJsonPath, FuzzerInput.ToString());
           
        }
    }
}
