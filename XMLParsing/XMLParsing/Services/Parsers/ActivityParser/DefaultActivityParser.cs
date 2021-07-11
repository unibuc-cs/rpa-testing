using System;
using System.Activities;
using System.Activities.Presentation.Annotations;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class DefaultActivityParser : IActivityParser
    {

        public void BeforeParsing(Activity activity, Graph graph, WorkflowData workflowData)
        {
            string annotationText = Annotation.GetAnnotationText(activity);
            string variableAnnotation = AnnotationHelper.TryExtractVariableAnnotation(annotationText);
            if(variableAnnotation != null)
            {
                workflowData.VariablesAnnotation = variableAnnotation;
            }
        }

        public Tuple<Node, Node> ParseActivity(Activity activity, Graph graph, WorkflowData workflowData)
        {
            BeforeParsing(activity, graph, workflowData);
            return ParseImplementation(activity, graph, workflowData);
        }

        public virtual Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            graph.Nodes.Add(node);
            return Tuple.Create(node, node);
        }


    }
}
