using System;
using System.Activities;
using System.Activities.Presentation.Annotations;
using System.Activities.XamlIntegration;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Xaml;
using UiPath.Core.Activities;
using UiPath.CSV.Activities;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services
{
    class WorkflowParser
    {

        private static readonly Lazy<WorkflowParser> LazyInstance = new Lazy<WorkflowParser>(() => new WorkflowParser());

        private WorkflowParser()
        {
            // Load needed assemblies. It would be nice if at some point, this would be done dynamically
            // UiPath.System.Activities
            LogMessage lm = new LogMessage();
            Assembly.LoadFrom(lm.GetType().Assembly.Location);

            ReadCsvFile rcf = new ReadCsvFile();
            Assembly.LoadFrom(rcf.GetType().Assembly.Location);

            System.Windows.Media.PointCollection pc = new System.Windows.Media.PointCollection();
            Assembly.LoadFrom(pc.GetType().Assembly.Location);

            OpenBrowser openBrowser = new OpenBrowser();
            Assembly.LoadFrom(openBrowser.GetType().Assembly.Location);

            UiPath.Mail.IMAP.Activities.GetIMAPMailMessages mail = new UiPath.Mail.IMAP.Activities.GetIMAPMailMessages();
            Assembly.LoadFrom(mail.GetType().Assembly.Location);

            System.Net.Mail.MailMessage mailMessage = new System.Net.Mail.MailMessage();
            Assembly.LoadFrom(mailMessage.GetType().Assembly.Location);

            ForEach<System.Net.Mail.MailMessage> x1 = new ForEach<System.Net.Mail.MailMessage>();
            Assembly.LoadFrom(x1.GetType().Assembly.Location);

            UiPath.PDF.Activities.ReadPDFText z = new UiPath.PDF.Activities.ReadPDFText();
            Assembly.LoadFrom(z.GetType().Assembly.Location);

            Console.WriteLine(x1.GetType().FullName);
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

        public Graph ParseGraph(string path)
        {
            AppDomain.CurrentDomain.AssemblyResolve += (_, args) => LatestOrDefault(args.Name);
            Graph graph = new Graph();
            WorkflowData mainWorkflowData = ParseWorkflow(graph, path);
            graph.StartNode = mainWorkflowData.StartNode;
            graph.EndNode = mainWorkflowData.EndNode;
            return graph;
        }

        public WorkflowData ParseWorkflow(Graph graph, string path)
        {
            string readText = File.ReadAllText(path);
            var stringReader = new StringReader(readText);
            var xamlXmlReader = new XamlXmlReader(stringReader);
            var xamlReader = ActivityXamlServices.CreateBuilderReader(xamlXmlReader);

            ActivityBuilder activityBuilder = XamlServices.Load(xamlReader) as ActivityBuilder;
            if (activityBuilder == null)
            {
                return null;
            }

            string s = Annotation.GetAnnotationText(activityBuilder);

            var workflowData = new WorkflowData(ActivityUtils.SanitizeString(activityBuilder.Name));

            if (ActivityUtils.IsFullPath(path))
            {
                workflowData.FullPath = path;
            }
            else
            {
                workflowData.FullPath = Path.GetFullPath(Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location) + "\\" + path);
            }

            // Arguments
            foreach (var dynamicActivityProperty in activityBuilder.Properties)
            {
                workflowData.Arguments.Add(dynamicActivityProperty);
            }

            Activity activity = activityBuilder.Implementation;
            IActivityParser parser = ActivityParserFactory.Instance.GetParser(activity);
            var ( startNode, endNode ) = parser.ParseActivity(activity, graph, workflowData);
            workflowData.StartNode = startNode;
            workflowData.EndNode = endNode;

            graph.WorkflowsData.Add(workflowData);

            return workflowData;
        }

    }
}
