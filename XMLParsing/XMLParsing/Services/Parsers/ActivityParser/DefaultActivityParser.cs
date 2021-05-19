using System;
using System.Activities;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class DefaultActivityParser : IActivityParser
    {
        public Tuple<Node, Node> ParseActivity(Activity activity, Workflow workflow)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity);
            workflow.Nodes.Add(node);
            return Tuple.Create(node, node);
        }
    }
}
