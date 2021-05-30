using System;
using System.Activities;
using System.Activities.Statements;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class AssignActivityParser : IActivityParser
    {
        public Tuple<Node, Node> ParseActivity(Activity activity, Workflow workflow)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflow.DisplayName, workflow.FullPath);
            AssignWfNode assignNode = new AssignWfNode(node);
            workflow.Nodes.Add(assignNode);

            Assign assignActivity = activity as Assign;
            assignNode.To = ExpressionUtils.TryParseExpression(assignActivity.To);
            assignNode.Value = ExpressionUtils.TryParseExpression(assignActivity.Value);

            return Tuple.Create(assignNode as Node, assignNode as Node);
        }
    }
}
