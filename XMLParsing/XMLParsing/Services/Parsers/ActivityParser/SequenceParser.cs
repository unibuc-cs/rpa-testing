using System;
using System.Activities;
using System.Activities.Presentation.Annotations;
using System.Activities.Statements;
using System.Collections.Generic;
using XMLParsing.Common;
using XMLParsing.Services.Parsers.ActivityParser;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.NativeActivityParser
{
    class SequenceParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            NativeActivity nativeActivity = activity as NativeActivity;
            if (nativeActivity == null || !nativeActivity.GetType().Equals(typeof(Sequence)))
            {
                throw new XamlParserException("Unexpected type of activity");
            }

            Sequence sequence = nativeActivity as Sequence;

            // Parse variables
            foreach (var variable in sequence.Variables)
            {
                workflowData.Variables.Add(variable);
            }

            Node startNode = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            graph.Nodes.Add(startNode);

            if(sequence.Activities == null || sequence.Activities.Count == 0)
            {
                return Tuple.Create(startNode, startNode);
            }

            List<Tuple<Node, Node>> innerActivitiesEnds = new List<Tuple<Node, Node>>();
            for (int i = 0; i < sequence.Activities.Count; i++)
            {
                IActivityParser parser = ActivityParserFactory.Instance.GetParser(sequence.Activities[i]);
                innerActivitiesEnds.Add(parser.ParseActivity(sequence.Activities[i], graph, workflowData));
            }

            // At this point, we have at least one activity, therefore at least one item inside innerActivitiesEnds
            Common.Transition startTransition = new Common.Transition();
            startTransition.Source = startNode;
            startTransition.Destination = innerActivitiesEnds[0].Item1;
            startTransition.Expression = "";
            startTransition.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
            graph.Transitions.Add(startTransition);

            for (int i = 1; i < innerActivitiesEnds.Count; i++)
            {
                Common.Transition transition = new Common.Transition();
                transition.Source = innerActivitiesEnds[i - 1].Item2;
                transition.Destination = innerActivitiesEnds[i].Item1;
                transition.Expression = "";
                transition.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(transition);
            }

            return Tuple.Create(startNode, innerActivitiesEnds[innerActivitiesEnds.Count - 1].Item2);
        }
    }
}
