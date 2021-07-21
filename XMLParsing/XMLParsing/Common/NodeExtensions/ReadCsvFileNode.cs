using System.Collections.Generic;

namespace XMLParsing.Common.NodeExtensions
{
    class ReadCsvFileNode : Node, IRelevantNode
    {
        public string CsvFilePath;
        public string DataTable;

        public ReadCsvFileNode()
        {
        }

        public ReadCsvFileNode(Node other)
        {
            this.DisplayName = other.DisplayName;
            this.Expression = other.Expression;
            this.Id = other.Id;
            this.IsConditional = other.IsConditional;
        }

        public override void AddAdditionalNodeInformation(IDictionary<string, object> nodeInformation)
        {
            IDictionary<string, string> readCsvInfo = new Dictionary<string, string>();
            nodeInformation.Add("expression", DataTable + " = " + "LoadCSV(" + CsvFilePath + ")");
        }
    }
}
