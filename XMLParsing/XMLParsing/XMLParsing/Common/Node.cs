

using System.Collections.Generic;

namespace XMLParsing.Common
{
    class Node
    {
        public int Id { get; set; }
        public string DisplayName { get; set; }
        public List<Transition> TransitionList { get; set; }

        public Node() 
        {
            TransitionList = new List<Transition>();
        }
    }
}
