using System;
using System.Activities;
using System.Activities.Presentation.Annotations;
using System.Activities.Statements;
using System.Collections;
using System.Collections.Generic;
using System.Reflection;
using XMLParsing.Common;
using XMLParsing.Services.Parsers.ActivityParser;
using XMLParsing.Utils;


namespace XMLParsing.Services
{
    class FlowchartParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            NativeActivity nativeActivity = activity as NativeActivity;
            if(nativeActivity == null || ! nativeActivity.GetType().Equals(typeof(Flowchart)))
            {
                throw new XamlParserException("Unexpected type of activity");
            }

            Flowchart flowchart = nativeActivity as Flowchart;

            // Parse variables
            foreach (var variable in flowchart.Variables)
            {
                workflowData.Variables.Add(variable);
            }

            return ParseNodeStructure(flowchart, graph, workflowData);
        }

        private Tuple<Node, Node> ParseNodeStructure(Flowchart flowchart, Graph graph, WorkflowData workflowData)
        {
            Dictionary<FlowNode, Tuple<Node, Node>> nodes = new Dictionary<FlowNode, Tuple<Node, Node>>();

            foreach(var flowNode in flowchart.Nodes)
            {
                if(flowNode is FlowStep)
                {
                    Activity activity = (flowNode as FlowStep).Action;
                    IActivityParser activityParser = ActivityParserFactory.Instance.GetParser(activity);
                    var activityEnds = activityParser.ParseActivity(activity, graph, workflowData);
                    nodes[flowNode] = activityEnds;
                }
                else
                {
                    Node node = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
                    nodes[flowNode] = Tuple.Create(node, node);
                    graph.Nodes.Add(node);
                }
            }


            Node startNode = nodes[flowchart.StartNode].Item1;
            Node endNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);

            foreach (var flowNode in flowchart.Nodes)
            {
                ParseFlowNode(flowNode, nodes, endNode, graph, workflowData);
            }

            endNode.DisplayName = workflowData.DisplayName + ":" + "Virtual_Flowchart_End";
            graph.Nodes.Add(endNode);

            return Tuple.Create(startNode, endNode);
        }

        public void ParseFlowNode(FlowNode flowNode, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Node endNode, Graph graph, WorkflowData workflowData)
        {
            if (flowNode == null)
            {
                return;
            }

            var flowNodeParserDict = new Dictionary<Type, Action>
            {
                { typeof(FlowDecision), () => ParseFlowDecision(flowNode as FlowDecision, nodes, endNode, graph, workflowData) },
                { typeof(FlowStep), () => ParseFlowStep(flowNode as FlowStep, nodes, endNode, graph, workflowData) },
            };

            if (flowNodeParserDict.ContainsKey(flowNode.GetType()))
            {
                flowNodeParserDict[flowNode.GetType()]();
            }
            else
            {
                // Leaving as default and try to use reflection on it
                ParseFlowSwitch(flowNode, nodes, endNode, graph, workflowData);
            }
        }

        public void ParseFlowDecision(FlowDecision flowDecision, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Node endNode, Graph graph, WorkflowData workflowData)
        {
            nodes[flowDecision].Item1.DisplayName = workflowData.DisplayName + ":" + ActivityUtils.SanitizeString(flowDecision.DisplayName);
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

                // Check for expression annotation
                string annotationText = Annotation.GetAnnotationText(flowDecision);
                string expressionAnnotation = AnnotationHelper.TryExtractExpressionAnnotation(annotationText);
                if (expressionAnnotation != null && nodes[flowDecision].Item1 != null)
                {
                    nodes[flowDecision].Item1.ExpressionAnnotation = expressionAnnotation;
                }

                return t;
            };

            // Parse true branch
            if(flowDecision.True != null)
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = nodes[flowDecision.True].Item1;
                graph.Transitions.Add(t);
            } 
            else
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = endNode;
                graph.Transitions.Add(t);
            }

            // Parse false branch
            if (flowDecision.False != null)
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                t.Destination = nodes[flowDecision.False].Item1;
                graph.Transitions.Add(t);
            }
            else
            {
                Common.Transition t = buildPartialTransition();
                t.ExpressionValue = Common.Transition.FALSE_TRANSITION_VALUE;
                t.Destination = endNode;
                graph.Transitions.Add(t);
            }
        }

        public void ParseFlowStep(FlowStep flowStep, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Node endNode, Graph graph, WorkflowData workflowData)
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

            graph.Transitions.Add(t);
        }


        public void ParseFlowSwitch(FlowNode flowSwitch, Dictionary<FlowNode, Tuple<Node, Node>> nodes, Node endNode, Graph graph, WorkflowData workflowData)
        {
            if (flowSwitch == null)
            {
                return;
            }

            string displayName = workflowData.DisplayName + ":" + ActivityUtils.SanitizeString(ReflectionHelpers.CallMethod(flowSwitch, "get_DisplayName") as string);
            nodes[flowSwitch].Item1.DisplayName = displayName;
            nodes[flowSwitch].Item1.IsConditional = true;

            var expression = ReflectionHelpers.CallMethod(flowSwitch, "get_Expression");
            var expressionText = ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;

            // Check for expression annotation
            string annotationText = Annotation.GetAnnotationText(flowSwitch);
            string expressionAnnotation = AnnotationHelper.TryExtractExpressionAnnotation(annotationText);

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
                Node currentVirtualNode = ActivityUtils.CreateEmptyNode(workflowData.DisplayName);
                currentVirtualNode.DisplayName = displayName + "_Case_" + key.ToString();
                currentVirtualNode.IsConditional = true;
                currentVirtualNode.Expression = expressionText + " == " + key.ToString();
                currentVirtualNode.ExpressionAnnotation = expressionAnnotation + " == " + key.ToString();
                graph.Nodes.Add(currentVirtualNode);


                // Add transition to it's true case
                Common.Transition t = new Common.Transition();
                t.Source = currentVirtualNode;
                t.Expression = currentVirtualNode.Expression;
                t.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                t.Destination = nodes[value].Item1;

                treatedClauses.Add(t.Expression);
                graph.Transitions.Add(t);


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
                    graph.Transitions.Add(tLast);
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
                graph.Transitions.Add(t);

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

                graph.Transitions.Add(tEnd);
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
                graph.Transitions.Add(t);
            }

        }

    }
}
