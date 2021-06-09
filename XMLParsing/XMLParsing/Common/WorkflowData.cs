using System.Activities;
using System.Collections.Generic;

namespace XMLParsing.Common
{
    class WorkflowData
    {
        public static IDictionary<string, int> InvokedWorkflowCount = new Dictionary<string, int>();

        public string DisplayName { get; set; }

        public string FullPath { get; set; }

        public Node StartNode { get; set; }

        public Node EndNode { get; set; }

        public List<Variable> Variables { get; set; }

        public List<DynamicActivityProperty> Arguments { get; set; }

        public WorkflowData(string DisplayName)
        {
            Arguments = new List<DynamicActivityProperty>();
            Variables = new List<Variable>();

            int id = 1;
            if(InvokedWorkflowCount.ContainsKey(DisplayName))
            {
                id = InvokedWorkflowCount[DisplayName];
            }

            this.DisplayName = DisplayName + "_" + id;
            InvokedWorkflowCount[DisplayName] = id + 1;
        }
    }
}
