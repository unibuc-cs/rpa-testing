using System;
using System.Activities;
using System.Activities.XamlIntegration;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Xaml;
using UiPath.Core.Activities;
using XMLParsing.Common;

namespace XMLParsing.Services
{
    class WorkflowParser
    {

        private static readonly Lazy<WorkflowParser> LazyInstance = new Lazy<WorkflowParser>(() => new WorkflowParser());

        private WorkflowParser()
        {
            // Load needed assemblies. It would be nice if at some point, this would be done dinamically
            // UiPath.System.Activities
            LogMessage lm = new LogMessage();
            Assembly.LoadFrom(lm.GetType().Assembly.Location);
        }

        public static WorkflowParser Instance
        {
            get
            {
                return LazyInstance.Value;
            }
        }

        public Assembly LatestOrDefault(string name, IEnumerable<Assembly> assemblies = null)
        {
            if (assemblies == null)
            {
                assemblies = AppDomain.CurrentDomain.GetAssemblies();
            }
            var shortName = new AssemblyName(name).Name;
            var assembly =
                (from a in assemblies
                 let assemblyIdentity = a.GetName()
                 where assemblyIdentity.Name.Equals(shortName, StringComparison.OrdinalIgnoreCase)
                 orderby assemblyIdentity.Version descending
                 select a).FirstOrDefault();
            if (assembly != null)
            {
                Console.WriteLine($"Redirected {name} to {assembly}.");
            }
            return assembly;
        }

        public Workflow ParseWorkflow(string path)
        {
            string readText = File.ReadAllText(path);
            var stringReader = new StringReader(readText);
            var xamlXmlReader = new XamlXmlReader(stringReader);
            var xamlReader = ActivityXamlServices.CreateBuilderReader(xamlXmlReader);

            AppDomain.CurrentDomain.AssemblyResolve += (_, args) => LatestOrDefault(args.Name);
            ActivityBuilder activityBuilder = XamlServices.Load(xamlReader) as ActivityBuilder;


            if (activityBuilder == null)
            {
                return null;
            }

            Workflow workflow = new Workflow();

            workflow.DisplayName = activityBuilder.Implementation.DisplayName;

            // Arguments
            foreach (var dynamicActivityProperty in activityBuilder.Properties)
            {
                workflow.Arguments.Add(dynamicActivityProperty);
            }

            Activity activity = activityBuilder.Implementation;
            IActivityParser parser = ActivityParserFactory.Instance.GetParser(activity);
            var ( startNode, _ ) = parser.ParseActivity(activity, workflow);
            workflow.StartNode = startNode;

            return workflow;
        }

    }
}
