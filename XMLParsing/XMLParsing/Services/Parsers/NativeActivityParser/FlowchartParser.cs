using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.VisualBasic.Activities;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services
{
    class FlowchartParser : INativeActivityParser
    {
        public void ParseNativeActivity(NativeActivity nativeActivity, Workflow workflow)
        {

            if(nativeActivity == null || workflow == null || ! nativeActivity.GetType().Equals(typeof(Flowchart)))
            {
                return;
            }

            Flowchart flowchart = nativeActivity as Flowchart;

            // Parse variables
            foreach (var variable in flowchart.Variables)
            {
                workflow.Variables.Add(variable);
            }


            Dictionary<FlowNode, Node> nodes = ParseNodeStructure(flowchart, workflow);
            workflow.Nodes = nodes.Values.ToList();
        }

        Dictionary<FlowNode, Node> ParseNodeStructure(Flowchart flowchart, Workflow workflow)
        {
            Dictionary<FlowNode, Node> nodes = new Dictionary<FlowNode, Node>();

            var idGenerator = 0;
            foreach(var flowNode in flowchart.Nodes)
            {
                Node node = new Node();
                node.Id = idGenerator++;
                nodes[flowNode] = node;
            }

            foreach (var flowNode in flowchart.Nodes)
            {
                ParseFlowNode(flowNode, nodes, workflow);
            }

            return nodes;
        }

        public void ParseFlowNode(FlowNode flowNode, Dictionary<FlowNode, Node> node, Workflow workflow)
        {
            if (flowNode == null)
            {
                return;
            }

            var flowNodeParserDict = new Dictionary<Type, Action>
            {
                { typeof(FlowDecision), () => ParseFlowDecision(flowNode as FlowDecision, node, workflow) },
                { typeof(FlowStep), () => ParseFlowStep(flowNode as FlowStep, node, workflow) },
            };

            if (flowNodeParserDict.ContainsKey(flowNode.GetType()))
            {
                flowNodeParserDict[flowNode.GetType()]();
            }
            else
            {
                // Leaving as default and try to use reflection on it
                ParseFlowSwitch(flowNode, node, workflow);
            }
        }

        public void ParseFlowDecision(FlowDecision flowDecision, Dictionary<FlowNode, Node> nodes, Workflow workflow)
        {
            nodes[flowDecision].DisplayName = flowDecision.DisplayName;
            nodes[flowDecision].IsConditional = true;

            Func<Common.Transition> buildPartialTransition = () => 
            {
                Common.Transition t = new Common.Transition();
                t.source = nodes[flowDecision];

                // flowNode.Condition is an VisualBasicValue<Boolean> : Activity<bool>
                t.expression = "";

                PropertyInfo expressionTextInfo = flowDecision.Condition.GetType().GetProperty("ExpressionText");
                if (expressionTextInfo != null)
                {
                    t.expression = expressionTextInfo.GetValue(flowDecision.Condition) as String;
                }

                return t;
            };

            // Parse true branch
            if(flowDecision.True != null)
            {
                Common.Transition t = buildPartialTransition();
                t.expressionValue = "True";
                t.destination = nodes[flowDecision.True];
                workflow.Transitions.Add(t);
            }

            // Parse false branch
            if (flowDecision.False != null)
            {
                Common.Transition t = buildPartialTransition();
                t.expressionValue = "False";
                t.destination = nodes[flowDecision.False];
                workflow.Transitions.Add(t);
            }
        }

        public void ParseFlowStep(FlowStep flowStep, Dictionary<FlowNode, Node> nodes, Workflow workflow)
        {
            if(flowStep.Action != null)
            {
                nodes[flowStep].DisplayName = flowStep.Action.DisplayName;
                nodes[flowStep].IsConditional = false;
                if (flowStep.Next != null)
                {
                    Common.Transition t = new Common.Transition();
                    t.source = nodes[flowStep];

                    // flowStep proceeds anyway
                    t.expression = "True";

                    // flowStep proceeds anyway
                    t.expressionValue = "True";

                    t.destination = nodes[flowStep.Next];

                    workflow.Transitions.Add(t);
                }
            }
        }

        /*
         * When splitToConditionals is true, the switch should be decomposed to multiple if clauses
         */
        public void ParseFlowSwitch(FlowNode flowSwitch, Dictionary<FlowNode, Node> nodes, Workflow workflow)
        {
            if (flowSwitch == null)
            {
                return;
            }

            nodes[flowSwitch].DisplayName = ReflectionHelpers.CallMethod(flowSwitch, "get_DisplayName") as string;
            nodes[flowSwitch].IsConditional = true;

            var expression = ReflectionHelpers.CallMethod(flowSwitch, "get_Expression");
            var expressionText = ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;

            var cases = ReflectionHelpers.CallMethod(flowSwitch, "get_Cases") as IEnumerable;
            var defaultCase = ReflectionHelpers.CallMethod(flowSwitch, "get_Default") as FlowNode;


            List<string> treatedClauses = new List<string>();
            foreach(var flowCase in cases)
            {
                Common.Transition t = new Common.Transition();
                t.source = nodes[flowSwitch];

                var key = ReflectionHelpers.CallMethod(flowCase, "get_Key");

                t.expression = expressionText + " == " + key.ToString();
                t.expressionValue = "True";

                treatedClauses.Add(t.expression);

                var value = ReflectionHelpers.CallMethod(flowCase, "get_Value") as FlowNode;
                t.destination = nodes[value];

                workflow.Transitions.Add(t);
            }

            // Treat the default
            if (defaultCase != null)
            {
                Common.Transition t = new Common.Transition();
                t.source = nodes[flowSwitch];

                // flowStep proceeds anyway
                t.expression = "";

                t.expressionValue = "True";

                foreach (var treatedClause in treatedClauses)
                {
                    t.expression = t.expression + "!(" + treatedClause + ") and ";
                }

                if(t.expression == "")
                {
                    t.expression = "True";
                }
                else
                {
                    t.expression = t.expression.Substring(0, t.expression.Length - 5);
                }

                t.destination = nodes[defaultCase];

                workflow.Transitions.Add(t);
            }

        }

       
    }
}
