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
                    Node node = ActivityUtils.CreateEmptyNode(workflow.FullPath);
                    nodes[flowNode] = Tuple.Create(node, node);
                    workflow.Nodes.Add(node);
                }
            }


            Node startNode = nodes[flowchart.StartNode].Item1;
            Node endNode = ActivityUtils.CreateEmptyNode(workflow.FullPath);

            foreach (var flowNode in flowchart.Nodes)
            {
                ParseFlowNode(flowNode, nodes, workflow, endNode);
            }

            endNode.DisplayName = workflow.DisplayName + ":" + "Virtual_Flowchart_End";
            workflow.Nodes.Add(endNode);

            return Tuple.Create(startNode, endNode);
        }

        public void ParseFlowNode(FlowNode flowNode, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow, Node endNode)
        {
            if (flowNode == null)
            {
                return;
            }

            var flowNodeParserDict = new Dictionary<Type, Action>
            {
                { typeof(FlowDecision), () => ParseFlowDecision(flowNode as FlowDecision, nodes, workflow, endNode) },
                { typeof(FlowStep), () => ParseFlowStep(flowNode as FlowStep, nodes, workflow, endNode) },
            };

            if (flowNodeParserDict.ContainsKey(flowNode.GetType()))
            {
                flowNodeParserDict[flowNode.GetType()]();
            }
            else
            {
                // Leaving as default and try to use reflection on it
                ParseFlowSwitch(flowNode, nodes, workflow, endNode);
            }
        }

        public void ParseFlowDecision(FlowDecision flowDecision, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow, Node endNode)
        {
            nodes[flowDecision].Item1.DisplayName = workflow.DisplayName + ":" + ActivityUtils.SanitizeString(flowDecision.DisplayName);
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
            else
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = endNode;
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
            else
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                t.Destination = endNode;
                workflow.Transitions.Add(t);
            }
        }

        public void ParseFlowStep(FlowStep flowStep, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow, Node endNode)
        {
            // This one should treat only transitions, and not additional node information
            Common.Transition t = new Common.Transition();
            t.Source = nodes[flowStep].Item2;
            t.Expression = "";
            t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;

            if (flowStep.Next != null)
            {
                t.Destination = nodes[flowStep.Next].Item1;
            }
            else
            {
                t.Destination = endNode;
            }

            workflow.Transitions.Add(t);
        }


        public void ParseFlowSwitch(FlowNode flowSwitch, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Workflow workflow, Node endNode)
        {
            if (flowSwitch == null)
            {
                return;
            }

            string displayName = workflow.DisplayName + ":" + ActivityUtils.SanitizeString(ReflectionHelpers.CallMethod(flowSwitch, "get_DisplayName") as string);
            nodes[flowSwitch].Item1.DisplayName = displayName;
            nodes[flowSwitch].Item1.IsConditional = true;

            var expression = ReflectionHelpers.CallMethod(flowSwitch, "get_Expression");
            var expressionText = ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;

            var cases = ReflectionHelpers.CallMethod(flowSwitch, "get_Cases") as IEnumerable;
            var defaultCase = ReflectionHelpers.CallMethod(flowSwitch, "get_Default") as FlowNode;



            Node firstVirtualNode = null;
            Node lastVirtualNode = null;
            List<string> treatedClauses = new List<string>();
            foreach(var flowCase in cases)
            {
                var key = ReflectionHelpers.CallMethod(flowCase, "get_Key");
                var value = ReflectionHelpers.CallMethod(flowCase, "get_Value") as FlowNode;

                // Create a virtual Node
                Node currentVirtualNode = ActivityUtils.CreateEmptyNode(workflow.FullPath);
                currentVirtualNode.DisplayName = displayName + "_Case_" + key.ToString();
                currentVirtualNode.IsConditional = true;
                currentVirtualNode.Expression = expressionText + " == " + key.ToString();
                workflow.Nodes.Add(currentVirtualNode);


                // Add transition to it's true case
                Common.Transition t = new Common.Transition();
                t.Source = currentVirtualNode;
                t.Expression = currentVirtualNode.Expression;
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = nodes[value].Item1;

                treatedClauses.Add(t.Expression);
                workflow.Transitions.Add(t);


                if (firstVirtualNode == null)
                {
                    firstVirtualNode = currentVirtualNode;
                }

                if(lastVirtualNode != null)
                {
                    Common.Transition tLast = new Common.Transition();
                    tLast.Source = lastVirtualNode;
                    tLast.Expression = lastVirtualNode.Expression;
                    tLast.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                    tLast.Destination = currentVirtualNode;
                    workflow.Transitions.Add(tLast);
                }

                lastVirtualNode = currentVirtualNode;
            }

            if(lastVirtualNode != null)
            {
                // bind real flow node to the first virtual and the last virtual to the default, if one exists
                Common.Transition t = new Common.Transition();
                t.Source = nodes[flowSwitch].Item1;
                t.Expression = "";
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = firstVirtualNode;
                workflow.Transitions.Add(t);

                Common.Transition tEnd = new Common.Transition();
                tEnd.Source = lastVirtualNode;
                tEnd.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                tEnd.Expression = lastVirtualNode.Expression;

                if (defaultCase != null)
                {
                    tEnd.Destination = nodes[defaultCase].Item1;
                }
                else
                {
                    tEnd.Destination = endNode;
                }

                workflow.Transitions.Add(tEnd);
            }
            else
            {
                Common.Transition t = new Common.Transition();
                t.Source = nodes[flowSwitch].Item1;
                t.Expression = "";
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;

                if (defaultCase != null)
                {
                    t.Destination = nodes[defaultCase].Item1;
                }
                else
                {
                    t.Destination = endNode;
                }
                workflow.Transitions.Add(t);
            }

        }

    }
}
