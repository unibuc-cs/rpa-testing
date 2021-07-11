using System;
using System.Activities;
using System.Activities.Statements;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class AssignActivityParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            AssignWfNode assignNode = new AssignWfNode(node);
            graph.Nodes.Add(assignNode);

            Assign assignActivity = activity as Assign;
            assignNode.To = ExpressionUtils.TryParseExpression(assignActivity.To);
            assignNode.Value = ExpressionUtils.TryParseExpression(assignActivity.Value);

            return Tuple.Create(assignNode as Node, assignNode as Node);
        }
    }
}
