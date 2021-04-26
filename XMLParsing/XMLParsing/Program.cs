using System;
using XMLParsing.Common;
using XMLParsing.Services;

namespace XMLParsing
{
    class Program
    {

        static void Main(string[] args)
        {

            string path = @"..\..\..\..\Models\GenerateTestingData\Create Loan Process.xaml";
            try
            {

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
