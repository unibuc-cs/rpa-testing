using System;
using System.Activities;
using System.Activities.Presentation.Annotations;
using UiPath.CSV.Activities;
using XMLParsing.Common;
using XMLParsing.Common.NodeExtensions;
using XMLParsing.Utils;

namespace XMLParsing.Services.Parsers.ActivityParser
{
    class ReadCsvFileActivityParser : DefaultActivityParser
    {
        public override Tuple<Node, Node> ParseImplementation(Activity activity, Graph graph, WorkflowData workflowData)
        {
            Node node = ActivityUtils.CreateSimpleNodeFromActivity(activity, workflowData.DisplayName);
            ReadCsvFileNode assignNode = new ReadCsvFileNode(node);
            graph.Nodes.Add(assignNode);

            ReadCsvFile readCsvFile = activity as ReadCsvFile;
            assignNode.CsvFilePath = ExpressionUtils.TryParseExpression(readCsvFile.FilePath);
            assignNode.DataTable = ExpressionUtils.TryParseExpression(readCsvFile.DataTable);

            return Tuple.Create(assignNode as Node, assignNode as Node);
        }
    }
}
