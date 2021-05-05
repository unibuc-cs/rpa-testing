using System;
using System.Activities;
using System.Collections.Generic;

namespace XMLParsing.Common
{
    class Workflow
    {

        public List<DynamicActivityProperty> Arguments { get; set; }
        public List<Variable> Variables { get; set; }

        public string DisplayName { get; set; }

        public List<Node> Nodes { get; set; }

        public List<Transition> Transitions { get; set; }

        public Workflow()
        {
            Arguments = new List<DynamicActivityProperty>();
            Variables = new List<Variable>();
            Nodes = new List<Node>();
            Transitions = new List<Transition>();
        }
    }
}
