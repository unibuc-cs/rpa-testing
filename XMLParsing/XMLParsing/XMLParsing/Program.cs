using System;
using System.Collections.Generic;
using System.Linq;
using System.Xml.Linq;

namespace XMLParsing
{
    class Program
    {
        static void Main(string[] args)
        {
            var xml = System.Xml.Linq.XDocument.Load(@"C:\Users\Marina Cernat\Documents\GitHub\rpa-testing\GenerateTestingData\Create Loan Process.xaml");

            IEnumerable<XElement> firstNode = xml.Descendants();
            
            Console.WriteLine("Arguments: ");

            List<string> arguments = new List<string>();
            List<string> argumentsTypes = new List<string>();

            foreach (XElement innerNode in firstNode)
            {

                if (innerNode.Name.LocalName.Equals("Property"))
                {
                    String name = innerNode.Attribute("Name").Value.ToString();

                    Console.WriteLine(name);

                    arguments.Add(name);

                    IEnumerable<XAttribute> attributesType = innerNode.Attributes();
                    foreach (XAttribute attributeType in attributesType)
                    {
                        if (attributeType.Name.ToString().Contains("Type"))
                        {
                            String attType = attributeType.Value.ToString().Substring(attributeType.Value.ToString().IndexOf(':') + 1).Trim(')');
                            argumentsTypes.Add(attType);
                            
                        }

                    }

                }

            }

            Console.WriteLine();

            Console.WriteLine("Types of Arguments: ");

            foreach (string type in argumentsTypes)
            {
                Console.WriteLine(type);
            }

            Console.WriteLine();

            IEnumerable<XAttribute> attList = from at in firstNode.Attributes()
                                              where at.ToString().Contains("Condition")
                                              select at;

            List<string> conditions = new List<string>();
            List<string> variables = new List<string>();
            List<string> types = new List<string>();
            

            foreach (var attr in attList)
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

            foreach (XElement innerNode in firstNode)
            {

                if (innerNode.Name.LocalName.Equals("Variable"))
                {
                    String name = innerNode.Attribute("Name").Value.ToString();

                    variables.Add(name);

                    IEnumerable<XAttribute> attributesType = innerNode.Attributes();
                    foreach (XAttribute attributeType in attributesType)
                    {
                        if (attributeType.Name.ToString().Contains("TypeArguments"))
                        {
                            String attType = attributeType.Value.ToString().Substring(attributeType.Value.ToString().IndexOf(':') + 1);
                            types.Add(attType);

                        }

                    }

                }

            }

            Console.WriteLine("Model conditions:");
            Console.WriteLine("");

            foreach (String condition in conditions)
            {
                Console.WriteLine(condition);
                Console.WriteLine("");
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
            Console.WriteLine("Model variables:");
            Console.WriteLine("");

            foreach (String variable in variables)
            {
                Console.WriteLine(variable);
            }


            Console.WriteLine("\n");
            Console.WriteLine("Variables' data types:");
            Console.WriteLine("");

            foreach (String type in types)
            {
                Console.WriteLine(type);
            }


            Console.WriteLine("\n");
            Console.WriteLine("Variables present in conditions:");
            Console.WriteLine("");

            List<string> varInCond = new List<string>();

            foreach (String cond in conditions)
            {
                foreach (String var in variables)
                {
                    if (cond.Contains(var))
                    {
                        varInCond.Add(var);
                    }
                }
            }

            varInCond = varInCond.Distinct().ToList();

            foreach (String variable in varInCond)
            {
                Console.WriteLine(variable);
            }



            Console.WriteLine("\n");
            Console.WriteLine("Arguments present in conditions:");
            Console.WriteLine("");

            List<string> argInCond = new List<string>();

            foreach (String cond in conditions)
            {
                foreach (String arg in arguments)
                {
                    if (cond.Contains(arg))
                    {
                        argInCond.Add(arg);
                    }
                }
            }

            argInCond = argInCond.Distinct().ToList();

            foreach (String argument in argInCond)
            {
                Console.WriteLine(argument);
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
