using System.IO;
using XMLParsing.Common;

namespace XMLParsing.Services.Serializers
{
    interface IWorkflowSerializer
    {
        void SerializeWorkflow(Graph graph, TextWriter textWriter);
    }
}
