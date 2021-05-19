using System;
using System.IO;
using XMLParsing.Common;

namespace XMLParsing.Services.Serializers
{
    class FullGraphSerializer : IWorkflowSerializer
    {
        private static readonly string IN_ARGUMENT_TYPE_NAME = "InArgument";
        private static readonly string OUT_ARGUMENT_TYPE_NAME = "OutArgument";

        public void SerializeWorkflow(Workflow workflow, TextWriter textWriter)
        {
            string output = "Worflow: \n\n";
            output += GetArguments(workflow);
            output += GetVariables(workflow);
            output += GetStructure(workflow);
            textWriter.WriteLine(output);
        }

        private string GetArguments(Workflow workflow)
        {
            string output = "Arguments: \n\n";
            foreach (var dynamicActivityProperty in workflow.Arguments)
            {
                var name = dynamicActivityProperty.Name;

                var direction = "None";
                if (dynamicActivityProperty.Type.FullName.Contains(IN_ARGUMENT_TYPE_NAME))
                {
                    direction = "In";
                }
                else if (dynamicActivityProperty.Type.FullName.Contains(OUT_ARGUMENT_TYPE_NAME))
                {
                    direction = "Out";
                }
                else
                {
                    // not expected
                }


                var type = typeof(object).Name;
                if (dynamicActivityProperty.Type.GetGenericArguments().Length > 0)
                {
                    type = dynamicActivityProperty.Type.GetGenericArguments()[0].Name;
                }

                output += String.Format("Name: '{0}', Type: '{1}', Direction: '{2}'", name, type, direction) + "\n";
            }
            return output + "\n";
        }
        private string GetVariables(Workflow workflow)
        {
            string output = "Variables: \n";

            foreach (var variable in workflow.Variables)
            {
                output += String.Format("Name: '{0}', Type: '{1}'", variable.Name, variable.Type.Name) + "\n";
            }

            return output + "\n";
        }

        private string GetStructure(Workflow workflow)
        {
            string output = "Structure: \n\n";

            foreach (var node in workflow.Nodes)
            {
                output += String.Format("Node '{0}', DisplayName: '{1}'", node.Id, node.DisplayName) + "\n";
                output += "\tTransitions: \n";
                foreach (var transition in (workflow.Transitions.FindAll((t) => t.Source.Equals(node))))
                {
                    output += String.Format("\t\tDestination: Id '{0}', Expression '{1}', Value needed '{2}'\n", transition.Destination.Id, transition.Expression, transition.ExpressionValue);
                }
            }

            return output + "\n";
        }
    }
}
