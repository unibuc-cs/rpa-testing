using XMLParsing.Common;
using System.Activities;
using System;

namespace XMLParsing.Services
{
    interface IActivityParser
    {

        /**
         * Method should return a tuple formed by starting and ending node of the activity
         */
        Tuple<Node, Node> ParseActivity(Activity activity, Graph workflow, WorkflowData workflowData);

    }
}
