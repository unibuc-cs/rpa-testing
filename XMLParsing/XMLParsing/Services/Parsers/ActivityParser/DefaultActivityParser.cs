using System;
using System.Activities;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class DefaultActivityParser : IActivityParser
    {
        public Tuple<Node, Node> ParseActivity(Activity activity, Graph graph, WorkflowData workflowData)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            graph.Nodes.Add(node);
            return Tuple.Create(node, node);
        }
    }
}
