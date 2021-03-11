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
            var xml = System.Xml.Linq.XDocument.Load(@"C:\Users\Marina Cernat\Desktop\RobotModelRPATesting\RobotModelRPATesting\Main.xaml");

            IEnumerable<XElement> firstNode = xml.Descendants();


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

            Console.WriteLine("Conditiile modelului:");
            Console.WriteLine("");

            foreach (String condition in conditions)
            {
                Console.WriteLine(condition);
                Console.WriteLine("");
            }

            Console.WriteLine("\n\n");
            Console.WriteLine("Model variables:");
            Console.WriteLine("");

            foreach (String variable in variables)
            {
                Console.WriteLine(variable);
            }


            Console.WriteLine("\n\n");
            Console.WriteLine("Variables' data types:");
            Console.WriteLine("");

            foreach (String type in types)
            {
                Console.WriteLine(type);
            }


            Console.WriteLine("\n\n");
            Console.WriteLine("Variabilele care se afla in conditii:");
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

            Console.WriteLine("\n\n");
            Console.WriteLine("Expresia din switch si ramurile:");
            Console.WriteLine("");

            foreach (XElement innerNode in firstNode)
            {
                if (innerNode.Name.LocalName.Equals("FlowSwitch"))
                {

                    IEnumerable<XAttribute> att = innerNode.Attributes();

                    foreach (XAttribute a in att)
                    {
                        if (a.Name.Equals("Expression")){
                           
                            String name = a.Value.ToString();
                           // Console.WriteLine("Switch expression: " + name);
                        }
                       Console.WriteLine("Switch expression: " + a);
                    }
                }

                if (innerNode.Name.LocalName.Equals("FlowStep") && innerNode.FirstAttribute.Name.ToString().Contains("Key"))
                {
                    String name = innerNode.FirstAttribute.Value.ToString();

                    Console.WriteLine(name);
                }
            }
            Console.WriteLine("default");
            Console.WriteLine("");

            Console.ReadLine();
        }
    }
}
