using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using XMLParsing.Common;

namespace XMLParsing.Utils
{
    class ActivityUtils
    {
        static int ID_GENERATOR = 0;

        static public Node CreateSimpleNodeFromActivity(Activity activity)
        {
            if (activity == null)
            {
                return null;
            }

            Node node = CreateEmptyNode();
            node.DisplayName = GetDisplayNameSanitized(activity);
            return node;
        }

        static public Node CreateEmptyNode()
        {
            Node node = new Node();
            node.DisplayName = "";
            node.Id = ID_GENERATOR++;
            node.IsConditional = false;
            node.Expression = "";
            return node;
        }

        static public string GetDisplayNameSanitized(Activity activity)
        {
            if (activity == null)
            {
                return "";
            }

            return SanitizeString(activity.DisplayName);
        }

        static public string SanitizeString(string s)
        {
            return s.Replace(" ", "_");
        }

    }
}
