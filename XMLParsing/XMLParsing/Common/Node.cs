﻿using System.Collections.Generic;

namespace XMLParsing.Common
{
    class Node
    {
        public int Id { get; set; }
        public string DisplayName { get; set; }

        public bool IsConditional { get; set; }

        public string Expression { get; set; }
        public string ExpressionAnnotation { get; set; }

        public Node() 
        {
        }

        public virtual void AddAdditionalNodeInformation(IDictionary<string, object> nodeInformation)
        {
        }

    }
}
