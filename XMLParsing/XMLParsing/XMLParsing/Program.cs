using System;
using System.Collections.Generic;
using System.Linq;
using System.Xml.Linq;

namespace XMLParsing
{
    class Program
    {
        //Returns a dictionary with the name of the argument as key and the type of the argument as value.

        public static Dictionary<String, String> getNodes(IEnumerable<XElement> xamlElements, String element, String attribute, String type)
        {
            var nodes = new Dictionary<String, String>();
            
            foreach (XElement elem in xamlElements)
            {

                if (elem.Name.LocalName.Equals(element))
                {
                    String name = elem.Attribute(attribute).Value.ToString();
                    

                    IEnumerable<XAttribute> attributesType = elem.Attributes();
                    foreach (XAttribute attributeType in attributesType)
                    {
                        if (attributeType.Name.ToString().Contains(type))
                        {
                            String attType = attributeType.Value.ToString().Substring(attributeType.Value.ToString().IndexOf(':') + 1).Trim(')');

                            nodes.Add(name, attType);


                        }

                    }

                }

            }
           
            return nodes;
        }

        //Returns model conditions.
        public static List<String> getConditions(IEnumerable<XElement> xamlElements)
        {
            IEnumerable<XAttribute> conditionsList = from attribute in xamlElements.Attributes()
                                              where attribute.ToString().Contains("Condition")
                                              select attribute;

            List<string> conditions = new List<string>();


            foreach (var attr in conditionsList)
            {
                string condition;

                condition = attr.ToString();

                if (condition.Contains("Condition="))
                {
                    condition = condition.Replace("Condition=", "");
                }

                if (condition.Contains("\"["))
                {
                    condition = condition.Replace("\"[", "");
                }

                if (condition.Contains("]\""))
                {
                    condition = condition.Replace("]\"", "");
                }

                if (condition.Contains("&quot;"))
                {
                    condition = condition.Replace("&quot;", '"'.ToString());
                }

                if (condition.Contains("&lt;"))
                {
                    condition = condition.Replace("&lt;", "<");
                }

                if (condition.Contains("&gt;"))
                {
                    condition = condition.Replace("&gt;", ">");
                }

                conditions.Add(condition);
            }

            return conditions;
        }

        static void Main(string[] args)
        {
            var xml = System.Xml.Linq.XDocument.Load(@"C:\Users\Marina Cernat\Documents\GitHub\rpa-testing\GenerateTestingData\Create Loan Process.xaml");

            //--
            IEnumerable<XElement> firstNode = xml.Descendants();
            //--

            IEnumerable<XElement> xamlElements = xml.Descendants();

            Dictionary<String, String> arguments = getNodes(xamlElements, "Property", "Name", "Type");
            Dictionary<String, String> variables = getNodes(xamlElements, "Variable", "Name", "TypeArguments");
            List<String> conditions = getConditions(xamlElements);


            //------------------------------------------------------------
            Console.WriteLine("Arguments: ");

            foreach (KeyValuePair<String, String> arg in arguments)
            {
                Console.WriteLine("ArgumentName = {0}, ArgumentType = {1}", arg.Key, arg.Value);
            }

            Console.WriteLine();


            //------------------------------------------------------------
            Console.WriteLine("Variables: ");

            foreach (KeyValuePair<String, String> var in variables)
            {
                Console.WriteLine("VariableName = {0}, VariableType = {1}", var.Key, var.Value);
            }

            Console.WriteLine();


            //------------------------------------------------------------

            Console.WriteLine("Model conditions:");
            Console.WriteLine("");

            foreach (String condition in conditions)
            {
                Console.WriteLine(condition);
                Console.WriteLine("");
            }

            //------------------------------------------------------------


            Console.WriteLine("\n");
            Console.WriteLine("Variables present in conditions:");
            Console.WriteLine("");

            List<String> varInCond = new List<String>();

               foreach (String cond in conditions)
               {
                   foreach (KeyValuePair<String, String> var in variables)
                   {
                       if (cond.Contains(var.Key))
                       {
                           varInCond.Add(var.Key);
                       }
                   }
               }  

            varInCond = varInCond.Distinct().ToList();

            foreach (String variable in varInCond)
            {
                Console.WriteLine(variable);
            }


            //------------------------------------------------------------


            Console.WriteLine("\n");
            Console.WriteLine("Arguments present in conditions:");
            Console.WriteLine("");

            List<String> argInCond = new List<String>();

            foreach (String cond in conditions)
            {
                foreach (KeyValuePair<String, String> arg in arguments)
                {
                    if (cond.Contains(arg.Key))
                    {
                        argInCond.Add(arg.Key);
                    }
                }
            }

            argInCond = argInCond.Distinct().ToList();

            foreach (String argument in argInCond)
            {
                Console.WriteLine(argument);
            }



            

            /* Console.WriteLine("\n\n");
             Console.WriteLine("Conditions from While or DoWhile: ");
             Console.WriteLine(""); */

            foreach (XElement innerNode in firstNode)
            {

                if (innerNode.Name.LocalName.Equals("InterruptibleDoWhile.Condition"))
                {

                    IEnumerable<XElement> descendants = innerNode.Descendants();

                    IEnumerable<XAttribute> atLst = from at in descendants.Attributes()
                                                    where at.ToString().Contains("ExpressionText")
                                                    select at;

                    foreach (XAttribute at in atLst)
                    {

                        string condition;

                        condition = at.ToString();

                        if (condition.Contains("ExpressionText="))
                        {
                            condition = condition.Replace("ExpressionText=", "");
                        }

                        if (condition.Contains("\"["))
                        {
                            condition = condition.Replace("\"[", "");
                        }

                        if (condition.Contains("]\""))
                        {
                            condition = condition.Replace("]\"", "");
                        }

                        if (condition.Contains("&quot;"))
                        {
                            condition = condition.Replace("&quot;", '"'.ToString());
                        }

                        if (condition.Contains("&lt;"))
                        {
                            condition = condition.Replace("&lt;", "<");
                        }

                        if (condition.Contains("&gt;"))
                        {
                            condition = condition.Replace("&gt;", ">");
                        }

                        conditions.Add(condition);

                        Console.WriteLine(condition);
                    }
                }
            }

       
            Console.WriteLine("\n");
            Console.WriteLine("Switch expression and branches:");
            Console.WriteLine("");

            bool haveSwitch = false;

            foreach (XElement innerNode in firstNode)
            {
                if (innerNode.Name.LocalName.Equals("FlowSwitch"))
                {
                    haveSwitch = true;

                    IEnumerable<XAttribute> att = innerNode.Attributes();

                    foreach (XAttribute a in att)
                    {
                        if (a.Name.Equals("Expression")){
                           
                            String name = a.Value.ToString();
                           // Console.WriteLine("Switch expression: " + name);
                        }
                       Console.WriteLine("Switch expression: " + a);
                    }

                    Console.WriteLine("default");
                    Console.WriteLine("");
                }

                if (innerNode.Name.LocalName.Equals("FlowStep") && innerNode.FirstAttribute.Name.ToString().Contains("Key"))
                {
                    String name = innerNode.FirstAttribute.Value.ToString();

                    Console.WriteLine(name);
                }
            }

            if (haveSwitch == false)
            {
                Console.WriteLine("Not applicable");
            }

            Console.ReadLine();
        }
    }
}
