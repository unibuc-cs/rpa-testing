using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace XMLParsing.Common
{
    class Transition
    {
        public Node source { get; set; }
        public Node destination { get; set; }
        public String expression { get; set; }
        public String expressionValue { get; set; }
    }
}
