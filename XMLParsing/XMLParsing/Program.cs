using System;
using System.Collections.Generic;
using System.Linq;
using System.Xml.Linq;
using System.Activities;
using System.Activities.XamlIntegration;
using System.IO;
using System.Xaml;
using XMLParsing.Common;
using XMLParsing.Services;
using UiPath.Core.Activities;

namespace XMLParsing
{
    class Program
    {

        static void Main(string[] args)
        {

            string path = @"C:\UiPath\rpa-testing\GenerateTestingData\Create Loan Process.xaml";
            try
            {
                LogMessage lm;
                Workflow wf = WorkflowParser.Instance.ParseWorkflow(path);
                if(wf == null)
                {
                    Console.WriteLine("Error, workflow is null");
                    return;
                }
                Console.WriteLine(wf.ToString());
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.Message);
                Console.WriteLine(ex.StackTrace);
            }

            Console.ReadLine();

        }

    }
}
