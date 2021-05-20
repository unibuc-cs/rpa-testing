using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using XMLParsing.Common;
using XMLParsing.Utils;


namespace XMLParsing.Services
{
    class FlowchartParser : IActivityParser
    {
        public Tuple<Node, Node> ParseActivity(Activity activity, Workflow workflow)
        {
            NativeActivity nativeActivity = activity as NativeActivity;
            if(nativeActivity == null || workflow == null || ! nativeActivity.GetType().Equals(typeof(Flowchart)))
            {
                throw new XamlParserException("Unexpected type of activity");
            }

            Flowchart flowchart = nativeActivity as Flowchart;

            // Parse variables
            foreach (var variable in flowchart.Variables)
            {
                workflow.Variables.Add(variable);
            }

            return ParseNodeStructure(flowchart, workflow);
        }

        private Tuple<Node, Node> ParseNodeStructure(Flowchart flowchart, Workflow workflow)
        {
            Dictionary<FlowNode, Tuple<Node, Node>> nodes = new Dictionary<FlowNode, Tuple<Node, Node>>();

            foreach(var flowNode in flowchart.Nodes)
            {
                if(flowNode is FlowStep)
                {
                    Activity activity = (flowNode as FlowStep).Action;
                    IActivityParser activityParser = ActivityParserFactory.Instance.GetParser(activity);
                    var activityEnds = activityParser.ParseActivity(activity, workflow);
                    nodes[flowNode] = activityEnds;
                }
                else
                {
                    Node node = ActivityUtils.CreateEmptyNode();
                    nodes[flowNode] = Tuple.Create(node, node);
                    workflow.Nodes.Add(node);
                }
            }


            // End node will be populated only if we encounter a case when a Flowchart can be nested inside another structure
            Node startNode = nodes[flowchart.StartNode].Item1;
            Node endNode = ActivityUtils.CreateEmptyNode();

            foreach (var flowNode in flowchart.Nodes)
            {
                ParseFlowNode(flowNode, nodes, workflow);
            }

            return Tuple.Create(startNode, endNode);
        }

        public void ParseFlowNode(FlowNode flowNode, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow)
        {
            if (flowNode == null)
            {
                return;
            }

            var flowNodeParserDict = new Dictionary<Type, Action>
            {
                { typeof(FlowDecision), () => ParseFlowDecision(flowNode as FlowDecision, nodes, workflow) },
                { typeof(FlowStep), () => ParseFlowStep(flowNode as FlowStep, nodes, workflow) },
            };

            if (flowNodeParserDict.ContainsKey(flowNode.GetType()))
            {
                flowNodeParserDict[flowNode.GetType()]();
            }
            else
            {
                // Leaving as default and try to use reflection on it
                ParseFlowSwitch(flowNode, nodes, workflow);
            }
        }

        public void ParseFlowDecision(FlowDecision flowDecision, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow)
        {
            nodes[flowDecision].Item1.DisplayName = ActivityUtils.SanitizeString(flowDecision.DisplayName);
            nodes[flowDecision].Item1.IsConditional = true;

            Func<Common.Transition> buildPartialTransition = () => 
            {
                Common.Transition t = new Common.Transition();
                t.Source = nodes[flowDecision].Item1;

                // flowNode.Condition is an VisualBasicValue<Boolean> : Activity<bool>
                t.Expression = "";

                PropertyInfo expressionTextInfo = flowDecision.Condition.GetType().GetProperty("ExpressionText");
                if (expressionTextInfo != null)
                {
                    t.Expression = expressionTextInfo.GetValue(flowDecision.Condition) as string;
                    if(t.Expression != null)
                    {
                        t.Expression = t.Expression;
                        nodes[flowDecision].Item1.Expression = t.Expression;
                    }
                }

                return t;
            };

            // Parse true branch
            if(flowDecision.True != null)
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = nodes[flowDecision.True].Item1;
                workflow.Transitions.Add(t);
            }

            // Parse false branch
            if (flowDecision.False != null)
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                t.Destination = nodes[flowDecision.False].Item1;
                workflow.Transitions.Add(t);
            }
        }

        public void ParseFlowStep(FlowStep flowStep, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow)
        {
            // This one should treat only transitions, and not additional node information

            if(flowStep.Next != null)
            {
                Common.Transition t = new Common.Transition();
                t.Source = nodes[flowStep].Item2;
                t.Expression = "";
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = nodes[flowStep.Next].Item1;
                workflow.Transitions.Add(t);
            }
        }

        /*
         * When splitToConditionals is true, the switch should be decomposed to multiple if clauses
         */
        public void ParseFlowSwitch(FlowNode flowSwitch, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow)
        {
            // TODO: split switches into ifs
            if (flowSwitch == null)
            {
                return;
            }

            string displayName = ActivityUtils.SanitizeString(ReflectionHelpers.CallMethod(flowSwitch, "get_DisplayName") as string);
            nodes[flowSwitch].Item1.DisplayName = displayName;
            nodes[flowSwitch].Item1.IsConditional = true;

            var expression = ReflectionHelpers.CallMethod(flowSwitch, "get_Expression");
            var expressionText = ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;

            var cases = ReflectionHelpers.CallMethod(flowSwitch, "get_Cases") as IEnumerable;
            var defaultCase = ReflectionHelpers.CallMethod(flowSwitch, "get_Default") as FlowNode;


            List<string> treatedClauses = new List<string>();
            foreach(var flowCase in cases)
            {
                Common.Transition t = new Common.Transition();
                t.Source = nodes[flowSwitch].Item1;

                var key = ReflectionHelpers.CallMethod(flowCase, "get_Key");

                t.Expression = expressionText + " == " + key.ToString();
                t.ExpressionValue = "True";

                treatedClauses.Add(t.Expression);

                var value = ReflectionHelpers.CallMethod(flowCase, "get_Value") as FlowNode;
                t.Destination = nodes[value].Item1;

                workflow.Transitions.Add(t);
            }

            // Treat the default
            if (defaultCase != null)
            {
                Common.Transition t = new Common.Transition();
                t.Source = nodes[flowSwitch].Item1;

                // flowStep proceeds anyway
                t.Expression = "";

                t.ExpressionValue = "True";

                foreach (var treatedClause in treatedClauses)
                {
                    t.Expression = t.Expression + "!(" + treatedClause + ") and ";
                }

                if(t.Expression == "")
                {
                    t.Expression = "True";
                }
                else
                {
                    t.Expression = t.Expression.Substring(0, t.Expression.Length - 5);
                }

                t.Destination = nodes[defaultCase].Item1;

                workflow.Transitions.Add(t);
            }

        }

    }
}
