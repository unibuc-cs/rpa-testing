

using System.Collections.Generic;

namespace XMLParsing.Common
{
    class Node
    {
        public int Id { get; set; }
        public string DisplayName { get; set; }

        /// <summary>
        /// Currently based on the order given by the flowchart
        /// </summary>
        public int RealNodeID { get; set; }
        public bool IsConditional { get; set; }

        public Node() 
        {
        }
    }
}
