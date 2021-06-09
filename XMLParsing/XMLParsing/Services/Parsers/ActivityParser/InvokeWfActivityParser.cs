using System;
using System.Activities;
using System.IO;
using System.Reflection;
using UiPath.Core.Activities;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class InvokeWfActivityParser : IActivityParser
    {
        public Tuple<Node, Node> ParseActivity(Activity activity, Graph graph, WorkflowData workflowData)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            InvokeWfNode invokeNode = new InvokeWfNode(node);
            graph.Nodes.Add(invokeNode);
            Node nextNode = node;

            InvokeWorkflowFile invokeAct = activity as InvokeWorkflowFile;

            try
            {
                invokeNode.InvokedWorkflow = invokeAct.WorkflowFileName.Expression.ToString();
                foreach (var item in invokeAct.Arguments)
                {
                    var direction = item.Value.Direction.ToString();
                    var value = ExpressionUtils.TryParseExpression(item.Value);

                    invokeNode.VariableMapping.Add(Tuple.Create(item.Key, direction, value));
                }


                var (invokedWorkflowDisplayName, (startNode, endNode)) = ParseWfBlackBox(invokeNode.InvokedWorkflow, workflowData.FullPath, graph);
                invokeNode.InvokedWorkflowDisplayName = invokedWorkflowDisplayName;
                nextNode = endNode;

                // We need to add: a transition from node to startNode of the wf Node of the invoked wf into this one, and return is as end.
                Common.Transition transition = new Common.Transition();
                transition.Source = invokeNode;
                transition.Destination = startNode;
                transition.Expression = "";
                transition.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                graph.Transitions.Add(transition);

            }
            catch (Exception e) 
            {
                Console.WriteLine(e.Message);
            }

            return Tuple.Create(invokeNode as Node, nextNode as Node);
        }

        protected Tuple<string, Tuple<Node, Node>> ParseWfBlackBox(string wfToInvokePath, string currentWfFullPath, Graph graph)
        {
            string path;
            if (ActivityUtils.IsFullPath(wfToInvokePath))
            {
                path = wfToInvokePath;
            }
            else
            {
                var currentWfDirName = new FileInfo(currentWfFullPath).Directory.FullName;
                path = Path.GetFullPath(currentWfDirName + "\\" + wfToInvokePath);
            }

            WorkflowData invokedWorkflowData = WorkflowParser.Instance.ParseWorkflow(graph, path);
            var startNode = invokedWorkflowData.StartNode;
            var endNode = invokedWorkflowData.EndNode;

            return Tuple.Create(invokedWorkflowData.DisplayName, Tuple.Create(startNode, endNode));
        }
    }
}
