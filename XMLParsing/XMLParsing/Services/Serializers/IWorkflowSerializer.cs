using System.IO;
using XMLParsing.Common;

namespace XMLParsing.Services.Serializers
{
    interface IWorkflowSerializer
    {
        void SerializeWorkflow(Workflow workflow, TextWriter textWriter);
    }
}
