using System;
using System.Activities;
using System.Activities.XamlIntegration;
using System.IO;
using System.Xaml;
using System.Xml;
using UiPath.Core.Activities;
using XMLParsing.Common;

namespace XMLParsing.Services
{
    class WorkflowParser
    {

        private static readonly Lazy<WorkflowParser> LazyInstance = new Lazy<WorkflowParser>(() => new WorkflowParser());

        private WorkflowParser()
        {
        }

        public static WorkflowParser Instance
        {
            get
            {
                return LazyInstance.Value;
            }
        }

        public Workflow ParseWorkflow(string path)
        {
            string readText = File.ReadAllText(path);


            // here
            //xmlns.AddNamespace("ui", "http://schemas.uipath.com/workflow/activities");

            // XamlXmlNamespaceManager

            // var context = new XmlParserContext(null, xmlns, "", XmlSpace.Default);
            // XamlSchemaContext xamlSchemaContext = new XamlSchemaContext();
            // xamlSchemaContext.
            // var xamlXmlReader = new XamlXmlReader(new StringReader(readText), xamlSchemaContext);
            // xamlXmlReader.SchemaContext.GetAllXamlNamespaces()

            
            XamlXmlReaderSettings xamlXmlReaderSettings = new XamlXmlReaderSettings();
            LogMessage l = new LogMessage();
            xamlXmlReaderSettings.LocalAssembly = l.GetType().Assembly;

            var stringReader = new StringReader(readText);
            var xamlXmlReader = new XamlXmlReader(stringReader, xamlXmlReaderSettings);
            var xamlReader = ActivityXamlServices.CreateBuilderReader(xamlXmlReader);

            // UiPath.Core.Activities.

            ActivityBuilder activityBuilder = XamlServices.Load(xamlReader) as ActivityBuilder;

            if(activityBuilder == null)
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

           // Structure
           NativeActivity nativeActivity = activityBuilder.Implementation as NativeActivity;

            if(nativeActivity == null)
            {
                return null;
            }
            INativeActivityParser parser = NativeActivityParserFactory.Instance.GetParser(nativeActivity);
            parser.ParseNativeActivity(nativeActivity, workflow);

            return workflow;
        }

    }
}
