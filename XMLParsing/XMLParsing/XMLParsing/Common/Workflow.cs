using System;
using System.Activities;
using System.Collections.Generic;

namespace XMLParsing.Common
{
    class Workflow
    {
        private static readonly string IN_ARGUMENT_TYPE_NAME = "InArgument";
        private static readonly string OUT_ARGUMENT_TYPE_NAME = "OutArgument";

        public List<DynamicActivityProperty> Arguments { get; set; }
        public List<Variable> Variables { get; set; }

        public string DisplayName { get; set; }

        public List<Node> Nodes { get; set; }

        public Workflow()
        {
            Arguments = new List<DynamicActivityProperty>();
            Variables = new List<Variable>();
            Nodes = new List<Node>();
        }

        public override string ToString()
        {
            string output = "Worflow: \n\n";
            output += PrintArguments();
            output += PrintVariables();
            output += PrintStructure();
            return output;
        }

        private string PrintArguments()
        {
            string output = "Arguments: \n\n";
            foreach (var dynamicActivityProperty in Arguments)
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
        private string PrintVariables()
        {
            string output = "Variables: \n";

            foreach (var variable in Variables)
            {
                output += String.Format("Name: '{0}', Type: '{1}'", variable.Name, variable.Type.Name) + "\n";
            }

            return output + "\n";
        }

        private string PrintStructure()
        {
            string output = "Structure: \n\n";

            foreach (var node in Nodes)
            {
                output += String.Format("Node '{0}', DisplayName: '{1}'", node.Id, node.DisplayName) + "\n";
                output += "\tTransitions: \n";
                foreach (var transition in node.TransitionList)
                {
                    output += String.Format("\t\tDestination: Id '{0}', Expression '{1}', Value needed '{2}'\n", transition.destination.Id, transition.expression, transition.expressionValue);
                }
            }

            return output + "\n";
        }
    }
}
