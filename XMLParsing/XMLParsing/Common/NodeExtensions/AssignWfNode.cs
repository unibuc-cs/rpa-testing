using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace XMLParsing.Common.NodeExtensions
{
    class AssignWfNode : Node
    {
        public string To;
        public string Value;

        public AssignWfNode()
        {
        }

        public AssignWfNode(Node other)
        {
            this.DisplayName = other.DisplayName;
            this.Expression = other.Expression;
            this.Id = other.Id;
            this.IsConditional = other.IsConditional;
        }

        public override void AddAdditionalNodeInformation(IDictionary<string, object> nodeInformation)
        {
            IDictionary<string, string> assigninfo = new Dictionary<string, string>();
            assigninfo.Add("to", To);
            assigninfo.Add("value", Value);
            nodeInformation.Add("variableAssignments", assigninfo);
        }

    }
}
