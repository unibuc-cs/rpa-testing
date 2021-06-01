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

        public string InvokedWorkflowDisplayName { get; set; }

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

        public override void AddAdditionalNodeInformation(IDictionary<string, object> nodeInformation)
        {
            nodeInformation.Add("invokedWorkflow", InvokedWorkflow);
            nodeInformation.Add("invokedWorkflowDisplayName", InvokedWorkflowDisplayName);
            List<IDictionary<string, object>> variableMappingList = new List<IDictionary<string, object>>();

            foreach (var item in VariableMapping)
            {
                IDictionary<string, object> variableData = new Dictionary<string, object>();
                variableData.Add("destinationWfArg", item.Item1);
                variableData.Add("argumentType", item.Item2);
                variableData.Add("sourceWfValue", item.Item3);

                variableMappingList.Add(variableData);
            }
            nodeInformation.Add("variableMappings", variableMappingList.ToArray());
        }

    }
}
