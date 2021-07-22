using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using XMLParsing.Common;
using XMLParsing.Utils;

namespace XMLParsing.Services.Serializers
{
    class Z3FullGraphSerializer : IWorkflowSerializer
    {
        protected static readonly string IN_ARGUMENT_TYPE_NAME = "InArgument";
        protected static readonly string OUT_ARGUMENT_TYPE_NAME = "OutArgument";

        public void SerializeWorkflow(Graph graph, TextWriter textWriter)
        {
            IDictionary<string, object> dictionary = new Dictionary<string, object>();

            AddWorkflowsData(graph, dictionary);
            AddGraph(graph, dictionary);
            dictionary.Add("startNode", graph.StartNode.DisplayName + "_" + graph.StartNode.Id);

            var serialized = JsonConvert.SerializeObject(dictionary, Formatting.Indented);
            textWriter.WriteLine(serialized);
        }

        private object TryGetVariableAnnotationFrom(string variableName, string variablesAnnotations)
        {
            if (variableName == null || variablesAnnotations == null)
            {
                return null;
            }

            try
            {
                var jsonObj = JsonConvert.DeserializeObject(variablesAnnotations);
                if (jsonObj == null)
                {
                    return null;
                }

                return ((JObject)jsonObj).Value<object>(variableName);
            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                return null;
            }
        }

        private IDictionary<string, object> GetWorkflowDataVariables(WorkflowData workflowData)
        {
            IDictionary<string, object> variables = GetWorkflowArguments(workflowData);

            foreach (var variable in workflowData.Variables)
            {
                IDictionary<string, object> variableData = new Dictionary<string, object>();
                variableData.Add("Type", variable.Type.Name);
                if(variable.Default != null)
                {
                    variableData.Add("Default", ExpressionUtils.TryParseExpression(variable.Default));
                }

                var variableAnnotation = TryGetVariableAnnotationFrom(variable.Name, workflowData.VariablesAnnotation);
                if(variableAnnotation != null)
                {
                    variableData.Add("Annotation", variableAnnotation);
                }

                variables.Add(variable.Name, variableData);
            }

            return variables;
        }

        private IDictionary<string, object> GetWorkflowArguments(WorkflowData workflowData)
        {
            IDictionary<string, object> arguments = new Dictionary<string, object>();
            foreach (var dynamicActivityProperty in workflowData.Arguments)
            {
                var name = dynamicActivityProperty.Name;
                var type = typeof(object).Name;
                if (dynamicActivityProperty.Type.GetGenericArguments().Length > 0)
                {
                    type = dynamicActivityProperty.Type.GetGenericArguments()[0].Name;
                }

                IDictionary<string, object> argumentData = new Dictionary<string, object>();
                argumentData.Add("Type", type);
                if (dynamicActivityProperty.Value != null)
                {
                    argumentData.Add("Default", ExpressionUtils.TryParseExpression(dynamicActivityProperty.Value));
                }

                arguments.Add(name, argumentData);

            }
            return arguments;
        }

        private string[] GetWorkflowInputArgumentsArray(WorkflowData workflowData)
        {
            List<string> inputArguments = new List<string>();
            foreach (var dynamicActivityProperty in workflowData.Arguments)
            {
                var name = dynamicActivityProperty.Name;
                if(dynamicActivityProperty.Type.Name.Contains("In") && dynamicActivityProperty.Type.Name.Contains("Argument"))
                {
                    inputArguments.Add(name);
                }
            }
            return inputArguments.ToArray();
        }

        private IDictionary<string, object> GetWorkflowData(WorkflowData workflowData)
        {
            IDictionary<string, object> workflowDataMap = new Dictionary<string, object>();

            workflowDataMap.Add("variables", GetWorkflowDataVariables(workflowData));
            workflowDataMap.Add("inputArguments", GetWorkflowInputArgumentsArray(workflowData));
            workflowDataMap.Add("displayName", workflowData.DisplayName);
            workflowDataMap.Add("fullPath", workflowData.FullPath);
            workflowDataMap.Add("invokedBy", workflowData.InvokedBy != null ? workflowData.InvokedBy : "");
            workflowDataMap.Add("startNode", workflowData.StartNode.DisplayName + "_" + workflowData.StartNode.Id);
            // workflowDataMap.Add("endNode", workflowData.EndNode.DisplayName + "_" + workflowData.EndNode.Id);

            return workflowDataMap;
        }

        protected void AddWorkflowsData(Graph graph, IDictionary<string, object> dictionary)
        {
            List<IDictionary<string, object>> workflowsDataList = new List<IDictionary<string, object>>();
            graph.WorkflowsData.ForEach(workflowData =>
            {
                workflowsDataList.Add(GetWorkflowData(workflowData));
            });
            dictionary.Add("workflows", workflowsDataList.ToArray());
        }

        protected void AddGraph(Graph workflow, IDictionary<string, object> dictionary)
        {
            IDictionary<string, object> graph = new Dictionary<string, object>();
            foreach(var node in workflow.Nodes)
            {
                if(ShouldProcessNode(node))
                {
                    AddGraphNode(workflow, graph, node);
                }
            }
            dictionary.Add("graph", graph);
        }
        
        protected IDictionary<string, object> GetAnnotation(Node node)
        {
            IDictionary<string, object> nodeAnnotations = new Dictionary<string, object>();

            // 1. Expression annotation

            try
            {
                if (node.ExpressionAnnotation != null)
                {
                    var expressionJsonObj = (JObject) JsonConvert.DeserializeObject(node.ExpressionAnnotation);
                    if (expressionJsonObj != null)
                    {
                        foreach(var pair in expressionJsonObj)
                        {
                            nodeAnnotations[pair.Key] = pair.Value.ToObject<object>();
                        }
                    }
                }

            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                return null;
            }

            return nodeAnnotations;
        }

        protected void AddGraphNode(Graph graph, IDictionary<string, object> dictionary, Node node)
        {
            var nodeTransitions = graph.Transitions.FindAll(x => x.Source.Equals(node));
            var nodeLabel = node.DisplayName + "_" + node.Id;

            IDictionary<string, object> nodeInformation = new Dictionary<string, object>();
            if(node.Expression != null && node.Expression != "")
            {
                nodeInformation.Add("expression", node.Expression);
            }

            var annotations = GetAnnotation(node);
            if(annotations != null && annotations.Keys.Count != 0)
            {
                nodeInformation.Add("Annotation", annotations);
            }
            
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
            dictionary.Add(nodeLabel, nodeInformation);

        }

        protected virtual bool ShouldProcessNode(Node node)
        {
            return true;
        }

        protected virtual Node ProcessDestination(Graph workflow, Transition transition)
        {
            return transition.Destination;
        }


    }
}
