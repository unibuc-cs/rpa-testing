using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Newtonsoft.Json;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;
using XMLParsing.Utils;

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
            AddInvokedWorkflows(workflow, dictionary);
            AddGraph(workflow, dictionary);

            var serialized = JsonConvert.SerializeObject(dictionary);
            textWriter.WriteLine(serialized);
        }

        protected void AddInvokedWorkflows(Workflow workflow, IDictionary<string, object> dictionary)
        {
            dictionary.Add("invokedWorkflows", workflow.InvokedWorkflows.ToArray());
        }

        protected void AddVariables(Workflow workflow, IDictionary<string, object> dictionary)
        {
            IDictionary<string, object> variables = new Dictionary<string, object>();
            foreach (var dynamicActivityProperty in workflow.Arguments)
            {
                var name = dynamicActivityProperty.Name;
                var type = typeof(object).Name;
                if (dynamicActivityProperty.Type.GetGenericArguments().Length > 0)
                {
                    type = dynamicActivityProperty.Type.GetGenericArguments()[0].Name;
                }

                variables.Add(name, type);
                
            }

            foreach (var variable in workflow.Variables)
            {
                variables.Add(variable.Name, variable.Type.Name);
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
            dictionary.Add("displayName", workflow.DisplayName);
            dictionary.Add("startNode", workflow.StartNode.DisplayName + "_" + workflow.StartNode.Id);
            dictionary.Add("graph", graph);
        }


        protected void AddGraphNode(Workflow workflow, IDictionary<string, object> graph, Node node)
        {
            var nodeTransitions = workflow.Transitions.FindAll(x => x.Source.Equals(node));
            var nodeLabel = node.DisplayName + "_" + node.Id;

            IDictionary<string, object> nodeInformation = new Dictionary<string, object>();
            nodeInformation.Add("expression", node.Expression);

            List<IDictionary<string, object>> transitionDataList = new List<IDictionary<string, object>>();

            foreach (var transition in nodeTransitions)
            {
                IDictionary<string, object> transitionData = new Dictionary<string, object>();
                transitionData.Add("value", transition.ExpressionValue);
                string destinationLabel = transition.Destination.DisplayName + "_" + transition.Destination.Id;
                transitionData.Add("destination", destinationLabel);
                transitionDataList.Add(transitionData);
            }

            node.AddAdditionalNodeInformation(nodeInformation);

            nodeInformation.Add("transitions", transitionDataList.ToArray());
            graph.Add(nodeLabel, nodeInformation);

        }

        protected virtual bool ShouldProcessNode(Node node)
        {
            return true;
        }

        protected virtual Node ProcessDestination(Workflow workflow, Transition transition)
        {
            return transition.Destination;
        }


    }
}
