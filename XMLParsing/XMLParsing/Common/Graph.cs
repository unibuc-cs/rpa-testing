using System.Collections.Generic;

namespace XMLParsing.Common
{
    class Graph
    {
        public Node StartNode { get; set; }

        public Node EndNode { get; set; }

        public List<Transition> Transitions { get; set; }

        public List<Node> Nodes { get; set; }

        public List<WorkflowData> WorkflowsData { get; set; }


        public Graph()
        {
            Nodes = new List<Node>();
            Transitions = new List<Transition>();
            WorkflowsData = new List<WorkflowData>();
        }
    }
}
