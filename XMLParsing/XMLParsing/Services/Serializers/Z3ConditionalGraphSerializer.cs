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

        protected override Node ProcessDestination(Graph workflow, Transition transition)
        {
            return SinkToConditional(workflow, transition.Destination);
        }

        protected Node SinkToConditional(Graph workflow, Node node)
        {
            Node result = node;
            while (!result.IsConditional)
            {
                var transition = workflow.Transitions.Find(x => x.Source.Equals(result));
                if (transition == null)
                {
                    return null;
                }
                result = transition.Destination;
            }

            return result;
        }
    }
}
