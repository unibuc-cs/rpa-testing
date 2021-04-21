using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.VisualBasic.Activities;
using XMLParsing.Common;

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


            Dictionary<FlowNode, Node> nodes = ParseNodeStructure(flowchart);
            workflow.Nodes = nodes.Values.ToList();
        }

        Dictionary<FlowNode, Node> ParseNodeStructure(Flowchart flowchart)
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
                ParseFlowNode(flowNode, nodes);
            }

            return nodes;
        }

        public void ParseFlowNode(FlowNode flowNode, Dictionary<FlowNode, Node> node)
        {
            if (flowNode == null)
            {
                return;
            }

            var flowNodeParserDict = new Dictionary<Type, Action>
            {
                { typeof(FlowDecision), () => ParseFlowDecision(flowNode as FlowDecision, node) },
                { typeof(FlowStep), () => ParseFlowStep(flowNode as FlowStep, node) },
                { typeof(FlowSwitch<object>), () => ParseFlowSwitch(flowNode as FlowSwitch<object> , node) }
            };

            if (flowNodeParserDict.ContainsKey(flowNode.GetType()))
            {
                flowNodeParserDict[flowNode.GetType()]();
            }
            else
            {
                // matching type of generic types is hard, so flow switches will be treated this way for now
                // ParseFlowSwitch(flowNode, node);
            }
        }

        public void ParseFlowDecision(FlowDecision flowDecision, Dictionary<FlowNode, Node> nodes)
        {
            nodes[flowDecision].DisplayName = flowDecision.DisplayName;
            
            // Parse true branch
            if(flowDecision.True != null)
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

                // We are on the true branch
                t.expressionValue = "True";

                t.destination = nodes[flowDecision.True];

                nodes[flowDecision].TransitionList.Add(t);
            }

            // Parse false branch
            if (flowDecision.False != null)
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

                // We are on the true branch
                t.expressionValue = "False";

                t.destination = nodes[flowDecision.False];

                nodes[flowDecision].TransitionList.Add(t);
            }
        }

        public void ParseFlowStep(FlowStep flowStep, Dictionary<FlowNode, Node> nodes)
        {
            if(flowStep.Action != null)
            {
                nodes[flowStep].DisplayName = flowStep.Action.DisplayName;
                if(flowStep.Next != null)
                {
                    Common.Transition t = new Common.Transition();
                    t.source = nodes[flowStep];

                    // flowStep proceeds anyway
                    t.expression = "True";

                    // flowStep proceeds anyway
                    t.expressionValue = "True";

                    t.destination = nodes[flowStep.Next];

                    nodes[flowStep].TransitionList.Add(t);
                }
            }
        }

        public void ParseFlowSwitch<T>(FlowSwitch<T> flowSwitch, Dictionary<FlowNode, Node> nodes)
        {
            nodes[flowSwitch].DisplayName = flowSwitch.DisplayName;

            var expression = flowSwitch.Expression.DisplayName;

            List<string> treatedValues = new List<string>();
            foreach (var flowCase in flowSwitch.Cases)
            {
                Common.Transition t = new Common.Transition();
                t.source = nodes[flowSwitch];

                t.expression = expression;

                t.expressionValue = flowCase.Key.ToString();

                treatedValues.Add(t.expressionValue);

                t.destination = nodes[flowCase.Value];

                nodes[flowSwitch].TransitionList.Add(t);
            }

            // Tread the default
            if (flowSwitch.Default != null)
            {
                Common.Transition t = new Common.Transition();
                t.source = nodes[flowSwitch];

                // flowStep proceeds anyway
                t.expression = "False ";

                t.expressionValue = "False";

                foreach (var treatedValue in treatedValues)
                {
                    t.expression = t.expression + " OR " + expression + ".Equals(" + treatedValue + ")";
                }

                t.destination = nodes[flowSwitch.Default];

                nodes[flowSwitch].TransitionList.Add(t);
            }

        }

       
    }
}
