using System;
using System.Activities;
using System.Activities.Presentation.Annotations;
using System.Activities.Statements;
using UiPath.Core.Activities;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class InterruptibleDoWhileActivityParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            InterruptibleDoWhile doWhileActivity = activity as InterruptibleDoWhile;

            Node conditional = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            conditional.Expression = ExpressionUtils.TryParseExpression(doWhileActivity.Condition);
            string annotationText = Annotation.GetAnnotationText(doWhileActivity);
            string expressionAnnotation = AnnotationHelper.TryExtractExpressionAnnotation(annotationText);
            conditional.ExpressionAnnotation = expressionAnnotation;
            conditional.IsConditional = true;

            graph.Nodes.Add(conditional);

            Activity body = doWhileActivity.Body;
            IActivityParser parser = ActivityParserFactory.Instance.GetParser(body);
            var (innerStart, innerEnd) = parser.ParseActivity(body, graph, workflowData);

            // Add a true transition from condition to body
            Common.Transition t = new Common.Transition();
            t.Source = conditional;
            t.Destination = innerStart;
            t.Expression = conditional.Expression;
            t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
            graph.Transitions.Add(t);

            // Add a true transition from body end to conditional
            Common.Transition t2 = new Common.Transition();
            t2.Source = innerEnd;
            t2.Destination = conditional;
            t2.Expression = "";
            t2.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
            graph.Transitions.Add(t2);

            // Need a virtual node which represents the end of the while block; Add a false transition from condition to end node
            Node endNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
            endNode.DisplayName = workflowData.DisplayName + ":" + "Virtual_DoWhile_End";
            graph.Nodes.Add(endNode);

            Common.Transition t3 = new Common.Transition();
            t3.Source = conditional;
            t3.Destination = endNode;
            t3.Expression = conditional.Expression;
            t3.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
            graph.Transitions.Add(t3);

            return Tuple.Create(innerStart, endNode);
        }
    }
}
