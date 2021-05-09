using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Newtonsoft.Json;
using XMLParsing.Common;

namespace XMLParsing.Services.Serializers
{
    class Z3FullGraphSerializer : IWorkflowSerializer
    {
        protected static readonly string IN_ARGUMENT_TYPE_NAME = "InArgument";
        protected static readonly string OUT_ARGUMENT_TYPE_NAME = "OutArgument";

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
        protected void AddVariables(Workflow workflow, IDictionary<string, object> dictionary)
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

        protected void AddGraph(Workflow workflow, IDictionary<string, object> dictionary)
        {
            IDictionary<string, object> graph = new Dictionary<string, object>();
            foreach(var node in workflow.Nodes)
            {
                if(ShouldProcessNode(node))
                {
                    AddGraphNode(workflow, graph, node);
                }
            }

            AddSinkNodes(graph);

            dictionary.Add("graph", graph);
        }

        protected void AddSinkNodes(IDictionary<string, object> graph)
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

        protected void AddGraphNode(Workflow workflow, IDictionary<string, object> graph, Node node)
        {
            var nodeTransitions = workflow.Transitions.FindAll(x => x.source.Equals(node)).GroupBy(x => x.expression);
            var nodeLabel = node.DisplayName.Replace(" ", "_");
            var count = 0;
            var sinkF = "sinkF";
            var sinkT = "sinkT";

            foreach (var result in nodeTransitions)
            {
                var expression = result.Key;
                Node falseDestination = null;
                Node trueDestination = null;
                foreach (var transition in result)
                {
                    if(transition.expressionValue.Equals("True"))
                    {
                        trueDestination = ProcessDestination(workflow, transition);
                    }
                    if(transition.expressionValue.Equals("False"))
                    {
                        falseDestination = ProcessDestination(workflow, transition);
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
                List<IDictionary<string, object>> transitionDataList = new List<IDictionary<string, object>>();
                nodeInformation.Add("realNodeID", node.RealNodeID);

                if (node.IsConditional)
                {
                    nodeInformation.Add("expression", expression);

                    IDictionary<string, object> falseTransitionData = new Dictionary<string, object>();
                    falseTransitionData.Add("value", "False");
                    falseTransitionData.Add("destination", falseDestinationLabel);
                    transitionDataList.Add(falseTransitionData);
                    
                }
                else
                {
                    nodeInformation.Add("expression", "");
                }

                IDictionary<string, object> trueTransitionData = new Dictionary<string, object>();
                trueTransitionData.Add("value", "True");
                trueTransitionData.Add("destination", trueDestinationLabel);
                transitionDataList.Add(trueTransitionData);

                nodeInformation.Add("transitions", transitionDataList.ToArray());
                graph.Add(currentNodeLabel, nodeInformation);
            }
        }

        

        protected virtual bool ShouldProcessNode(Node node)
        {
            return true;
        }

        protected virtual Node ProcessDestination(Workflow workflow, Transition transition)
        {
            return transition.destination;
        }


    }
}
