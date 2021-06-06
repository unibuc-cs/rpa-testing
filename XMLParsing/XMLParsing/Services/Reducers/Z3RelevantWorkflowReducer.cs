using System.Collections.Generic;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;

namespace XMLParsing.Services.Reducers
{
    class Z3RelevantWorkflowReducer : IWorkflowReducer
    {
        public void ReduceWorkflow(Workflow workflow)
        {
            List<Node> toReduce = new List<Node>();
            workflow.Nodes.ForEach(node =>
            {
                if (TryReduceNode(workflow, node))
                {
                    toReduce.Add(node);
                }
            });

            toReduce.ForEach(node => workflow.Nodes.Remove(node));
        }

        private bool TryReduceNode(Workflow workflow, Node node)
        {
            if(node.Equals(workflow.StartNode) || node.Equals(workflow.EndNode))
            {
                // Don't reduce if global start or end
                return false;
            }

            IRelevantNode relevantNode = node as IRelevantNode;
            if(relevantNode != null)
            {
                // Don't reduce if relevant
                return false;
            }

            if (node.IsConditional == true)
            {
                // Don't reduce if conditional
                return false;
            }

            if (!node.DisplayName.StartsWith(workflow.DisplayName))
            {
                // Node makes connections across workflows, do not remove
                return false;
            }

            // We should only be left with nodes that may have multiple entries but have maximum one output transition
            Transition outTransition = workflow.Transitions.Find(p => p.Source.Equals(node));

            List<Transition> inputTransitions = workflow.Transitions.FindAll(p => p.Destination.Equals(node));
            if(outTransition == null)
            {
                workflow.Transitions.RemoveAll(p => p.Destination.Equals(node));
            }
            else
            {
                workflow.Transitions.FindAll(p => p.Destination.Equals(node)).ForEach(p => p.Destination = outTransition.Destination);
            }

            return true;
        }
    }
}
