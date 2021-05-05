using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Newtonsoft.Json;
using XMLParsing.Common;

namespace XMLParsing.Services.Serializers
{
    class Z3ConditionalGraphSerializer : IWorkflowSerializer
    {
        private static readonly string IN_ARGUMENT_TYPE_NAME = "InArgument";
        private static readonly string OUT_ARGUMENT_TYPE_NAME = "OutArgument";

        public void SerializeWorkflow(Workflow workflow, TextWriter textWriter)
        {
            IDictionary<string, object> dictionary = new Dictionary<string, object>();


            AddVariables(workflow, dictionary);
            AddGraph(workflow, dictionary);

            var serialized = JsonConvert.SerializeObject(dictionary);
            textWriter.WriteLine(serialized);
        }

        /*
         * Variables are actually IN arguments
         */
        private void AddVariables(Workflow workflow, IDictionary<string, object> dictionary)
        {
            IDictionary<string, object> variables = new Dictionary<string, object>();
            foreach (var dynamicActivityProperty in workflow.Arguments)
            {
                var name = dynamicActivityProperty.Name;

                var direction = "None";
                if (dynamicActivityProperty.Type.FullName.Contains(IN_ARGUMENT_TYPE_NAME))
                {
                    direction = "In";
                }
                else if (dynamicActivityProperty.Type.FullName.Contains(OUT_ARGUMENT_TYPE_NAME))
                {
                    direction = "Out";
                }

                var type = typeof(object).Name;
                if (dynamicActivityProperty.Type.GetGenericArguments().Length > 0)
                {
                    type = dynamicActivityProperty.Type.GetGenericArguments()[0].Name;
                }

                if(direction.Equals("In"))
                {
                    variables.Add(name, type);
                }
            }
            dictionary.Add("variables", variables);
        }

        private void AddGraph(Workflow workflow, IDictionary<string, object> dictionary)
        {
            IDictionary<string, object> graph = new Dictionary<string, object>();
            foreach(var node in workflow.Nodes)
            {
                if(node.IsConditional)
                {
                    AddGraphNode(workflow, graph, node);
                }
            }

            AddSinkNodes(graph);

            dictionary.Add("graph", graph);
        }

        private void AddSinkNodes(IDictionary<string, object> graph)
        {
            IDictionary<string, object> trueNodeInformation = new Dictionary<string, object>();
            trueNodeInformation.Add("expression", "True");
            trueNodeInformation.Add("transitions", new object[] { });
            graph.Add("sinkT", trueNodeInformation);

            IDictionary<string, object> falseNodeInformation = new Dictionary<string, object>();
            falseNodeInformation.Add("expression", "True");
            falseNodeInformation.Add("transitions", new object[] { });
            graph.Add("sinkF", falseNodeInformation);
        }

        private void AddGraphNode(Workflow workflow, IDictionary<string, object> graph, Node node)
        {
            var nodeTransitions = workflow.Transitions.FindAll(x => x.source.Equals(node)).GroupBy(x => x.expression);
            var nodeLabel = node.DisplayName.Replace(" ", "_");
            var count = 0;
            var sinkF = "sinkF";
            var sinkT = "sinkT";

            // var lastNodeLabel = "";

            foreach (var result in nodeTransitions)
            {
                var expression = result.Key;
                Node falseDestination = null;
                Node trueDestination = null;
                foreach (var transition in result)
                {
                    if(transition.expressionValue.Equals("True"))
                    {
                        trueDestination = SinkToConditional(workflow, transition.destination);
                    }
                    if(transition.expressionValue.Equals("False"))
                    {
                        falseDestination = SinkToConditional(workflow, transition.destination);
                    }
                }

                var currentNodeLabel = nodeLabel;
                if (count > 0)
                {
                    currentNodeLabel = nodeLabel + "_" + count;
                }
                count++;

                var trueDestinationLabel = "";
                var falseDestinationLabel = "";

                if(trueDestination == null)
                {
                    trueDestinationLabel = sinkT;
                }
                else
                {
                    trueDestinationLabel = trueDestination.DisplayName.Replace(" ", "_");
                }

                if (count < nodeTransitions.Count())
                {
                    
                    falseDestinationLabel = nodeLabel + "_" + count;
                }
                else
                {
                    if (falseDestination == null)
                    {
                        falseDestinationLabel = sinkF;
                    }
                    else
                    {
                        falseDestinationLabel = falseDestination.DisplayName.Replace(" ", "_");
                    }
                }

                IDictionary<string, object> nodeInformation = new Dictionary<string, object> ();
                nodeInformation.Add("expression", expression);

                List<IDictionary<string, object>> transitionDataList = new List<IDictionary<string, object>>();

                IDictionary<string, object> falseTransitionData = new Dictionary<string, object>();
                falseTransitionData.Add("value", "False");
                falseTransitionData.Add("destination", falseDestinationLabel);
                transitionDataList.Add(falseTransitionData);

                IDictionary<string, object> trueTransitionData = new Dictionary<string, object>();
                trueTransitionData.Add("value", "True");
                trueTransitionData.Add("destination", trueDestinationLabel);
                transitionDataList.Add(trueTransitionData);

                nodeInformation.Add("transitions", transitionDataList.ToArray());
                graph.Add(currentNodeLabel, nodeInformation);
            }
        }

        private Node SinkToConditional(Workflow workflow, Node node)
        {
            Node result = node;
            while(!result.IsConditional)
            {
                var transition = workflow.Transitions.Find(x => x.source.Equals(result));
                if(transition == null)
                {
                    return null;
                }
                result = transition.destination;
            }

            return result;
        }


    }
}
