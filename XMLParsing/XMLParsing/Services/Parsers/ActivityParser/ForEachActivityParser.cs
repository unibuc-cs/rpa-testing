using System;
using System.Activities;
using UiPath.Core.Activities;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class ForEachActivityParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);

            // Reflection to get stuff out of node
            var Value = ReflectionHelpers.CallMethod(activity, "get_Values");

            // ForEachRow case
            ForEachRow ferAct = activity as ForEachRow;
            if(ferAct != null)
            {
                Value = ferAct.DataTable;
            }

            string collection = ExpressionUtils.TryParseExpression(Value);

            var Body = ReflectionHelpers.CallMethod(activity, "get_Body");
            var Argument = ReflectionHelpers.CallMethod(Body, "get_Argument");
            string item = ReflectionHelpers.CallMethod(Argument, "get_Name").ToString();

            node.Expression = "for " + item + " in " + collection;
            node.IsConditional = true;
            graph.Nodes.Add(node);

            Activity handler = ReflectionHelpers.CallMethod(Body, "get_Handler") as Activity;
            IActivityParser parser = ActivityParserFactory.Instance.GetParser(handler);
            var (innerStart, innerEnd) = parser.ParseActivity(handler, graph, workflowData);


            // Add a true transition from condition to body
            Common.Transition t = new Common.Transition();
            t.Source = node;
            t.Destination = innerStart;
            t.Expression = node.Expression;
            t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
            graph.Transitions.Add(t);

            // Add a true transition from body end to conditional
            Common.Transition t2 = new Common.Transition();
            t2.Source = innerEnd;
            t2.Destination = node;
            t2.Expression = "";
            t2.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
            graph.Transitions.Add(t2);

            // Need a virtual node which represents the end of the while block; Add a false transition from condition to end node
            Node endNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
            endNode.DisplayName = workflowData.DisplayName + ":" + "Virtual_ForEach_End";
            graph.Nodes.Add(endNode);

            Common.Transition t3 = new Common.Transition();
            t3.Source = node;
            t3.Destination = endNode;
            t3.Expression = node.Expression;
            t3.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
            graph.Transitions.Add(t3);

            return Tuple.Create(node, endNode);
        }
    }
}
