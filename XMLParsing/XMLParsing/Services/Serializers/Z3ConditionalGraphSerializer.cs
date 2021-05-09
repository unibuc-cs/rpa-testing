using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Newtonsoft.Json;
using XMLParsing.Common;

namespace XMLParsing.Services.Serializers
{
    class Z3ConditionalGraphSerializer : Z3FullGraphSerializer
    {
       
        protected override bool ShouldProcessNode(Node node)
        {
            return node.IsConditional;
        }

        protected override Node ProcessDestination(Workflow workflow, Transition transition)
        {
            return SinkToConditional(workflow, transition.destination);
        }

        protected Node SinkToConditional(Workflow workflow, Node node)
        {
            Node result = node;
            while (!result.IsConditional)
            {
                var transition = workflow.Transitions.Find(x => x.source.Equals(result));
                if (transition == null)
                {
                    return null;
                }
                result = transition.destination;
            }

            return result;
        }
    }
}
