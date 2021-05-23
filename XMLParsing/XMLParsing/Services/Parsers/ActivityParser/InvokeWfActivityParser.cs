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
        public Tuple<Node, Node> ParseActivity(Activity activity, Workflow workflow)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflow.DisplayName, workflow.FullPath);
            InvokeWfNode invokeNode = new InvokeWfNode(node);
            workflow.Nodes.Add(invokeNode);
            Node nextNode = node;

            InvokeWorkflowFile invokeAct = activity as InvokeWorkflowFile;

            try
            {
                invokeNode.InvokedWorkflow = invokeAct.WorkflowFileName.Expression.ToString();
                foreach (var item in invokeAct.Arguments)
                {
                    var direction = item.Value.Direction.ToString();
                    var value = "";
                    PropertyInfo expressionTextInfo = item.Value.Expression.GetType().GetProperty("ExpressionText");
                    if (expressionTextInfo != null)
                    {
                        value = expressionTextInfo.GetValue(item.Value.Expression) as string;
                    }
                    invokeNode.VariableMapping.Add(Tuple.Create(item.Key, direction, value));
                }


                var (startNode, endNode) = ParseWfBlackBox(invokeNode.InvokedWorkflow, workflow.FullPath);
                nextNode = endNode;

                // We need to add: a transition from node to startNode of the wf Node of the invoked wf into this one, and return is as end.
                Common.Transition transition = new Common.Transition();
                transition.Source = invokeNode;
                transition.Destination = startNode;
                transition.Expression = "";
                transition.ExpressionValue = Common.Transition.TRUE_TRANSITION_VALUE;
                workflow.Transitions.Add(transition);

                workflow.Nodes.Add(endNode);

            }
            catch (Exception e) 
            {
                Console.WriteLine(e.Message);
            }

            return Tuple.Create(invokeNode as Node, nextNode as Node);
        }

        protected Tuple<Node, Node> ParseWfBlackBox(string wfToInvokePath, string currentWfFullPath)
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

            Workflow invokedWorkflow = WorkflowParser.Instance.ParseWorkflow(path);
            var startNode = invokedWorkflow.StartNode;
            var endNode = invokedWorkflow.EndNode;

            return Tuple.Create(startNode, endNode);
        }
    }
}
