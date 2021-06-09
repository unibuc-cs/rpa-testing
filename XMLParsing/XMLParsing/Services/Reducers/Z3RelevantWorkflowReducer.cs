using System.Collections.Generic;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;

namespace XMLParsing.Services.Reducers
{
    class Z3RelevantWorkflowReducer : IWorkflowReducer
    {
        public void ReduceWorkflow(Graph graph)
        {
            List<Node> startEndNodes = new List<Node>();
            graph.WorkflowsData.ForEach(wfData =>
            {
                startEndNodes.Add(wfData.StartNode);
                startEndNodes.Add(wfData.EndNode);
            });


            List<Node> toReduce = new List<Node>();
            graph.Nodes.ForEach(node =>
            {
                if (!startEndNodes.Contains(node) && TryReduceNode(graph, node))
                {
                    toReduce.Add(node);
                }
            });

            toReduce.ForEach(node => graph.Nodes.Remove(node));
        }

        private bool TryReduceNode(Graph graph, Node node)
        {

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

            // We should only be left with nodes that may have multiple entries but have maximum one output transition
            Transition outTransition = graph.Transitions.Find(p => p.Source.Equals(node));

            List<Transition> inputTransitions = graph.Transitions.FindAll(p => p.Destination.Equals(node));
            if(outTransition == null)
            {
                graph.Transitions.RemoveAll(p => p.Destination.Equals(node));
            }
            else
            {
                graph.Transitions.FindAll(p => p.Destination.Equals(node)).ForEach(p => p.Destination = outTransition.Destination);
            }

            return true;
        }
    }
}
