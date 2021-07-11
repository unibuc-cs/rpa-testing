using System;
using System.Activities;
using System.Activities.Statements;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class IfActivityParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            If ifActivity = activity as If;

            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            graph.Nodes.Add(node);
            node.IsConditional = true;
            node.Expression = ExpressionUtils.TryParseExpression(ifActivity.Condition);

            Node endNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
            endNode.DisplayName = workflowData.DisplayName + ":" + "Virtual_If_End";
            graph.Nodes.Add(endNode);

            if (ifActivity.Then == null && ifActivity.Else == null)
            {
                Common.Transition t = new Common.Transition();
                t.Source = node;
                t.Destination = endNode;
                t.Expression = "";
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;

                node.Expression = ""; // We do this since lacking of if/else branches will just go to the next step
                graph.Transitions.Add(t);
                return Tuple.Create(node, node);
            }

            Func<Activity, Tuple<Node, Node>> parseInnerBranch = (branchActivity) =>
            {
                IActivityParser activityParser = ActivityParserFactory.Instance.GetParser(branchActivity);
                return activityParser.ParseActivity(branchActivity, graph, workflowData);
            };

            if(ifActivity.Then != null)
            {
                var (thenStart, thenEnd) = parseInnerBranch(ifActivity.Then);

                Common.Transition t1 = new Common.Transition();
                t1.Source = node;
                t1.Destination = thenStart;
                t1.Expression = node.Expression;
                t1.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(t1);

                Common.Transition t2 = new Common.Transition();
                t2.Source = thenEnd;
                t2.Destination = endNode;
                t2.Expression = "";
                t2.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(t2);
            }

            if (ifActivity.Else != null)
            {
                var (elseStart, elseEnd) = parseInnerBranch(ifActivity.Else);

                Common.Transition t1 = new Common.Transition();
                t1.Source = node;
                t1.Destination = elseStart;
                t1.Expression = node.Expression;
                t1.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                graph.Transitions.Add(t1);

                Common.Transition t2 = new Common.Transition();
                t2.Source = elseEnd;
                t2.Destination = endNode;
                t2.Expression = "";
                t2.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(t2);
            }

            return Tuple.Create(node, endNode);
        }
    }
}
