using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace XMLParsing.Common.NodeExtensions
{
    class InvokeWfNode : Node
    {

        public string InvokedWorkflow { get; set; }

        public IList<Tuple<string, string, string>> VariableMapping { get; set; }

        public InvokeWfNode()
        {
            VariableMapping = new List<Tuple<string, string, string>>();
        }

        public InvokeWfNode(Node other)
        {
            this.DisplayName = other.DisplayName;
            this.Expression = other.Expression;
            this.Id = other.Id;
            this.IsConditional = other.IsConditional;
            VariableMapping = new List<Tuple<string, string, string>>();
        }

    }
}
