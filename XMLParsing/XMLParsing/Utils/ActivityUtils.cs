﻿using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using XMLParsing.Common;
using Transition = System.Activities.Statements.Transition;

namespace XMLParsing.Utils
{
    class ActivityUtils
    {
        static IDictionary<string, int> ID_GENERATORS_MAP;

        static ActivityUtils()
        {
            ID_GENERATORS_MAP = new Dictionary<string, int>();
        }

        static public int GetNextId(string workflowFullPath)
        {
            if(ID_GENERATORS_MAP.ContainsKey(workflowFullPath))
            {
                ID_GENERATORS_MAP[workflowFullPath] = ID_GENERATORS_MAP[workflowFullPath] + 1;
            }
            else
            {
                ID_GENERATORS_MAP.Add(workflowFullPath, 1);
            }

            return ID_GENERATORS_MAP[workflowFullPath];
        }

        static public Node CreateSimpleNodeFromState(State state, string workflowDisplayName)
        {
            if (state == null)
            {
                return null;
            }

            Node node = CreateEmptyNode(workflowDisplayName);
            node.DisplayName = workflowDisplayName + ":" + GetDisplayNameSanitized(state);
            return node;
        }

        static public Node CreateSimpleNodeFromActivity(Activity activity, string workflowDisplayName)
        {
            if (activity == null)
            {
                return null;
            }

            Node node = CreateEmptyNode(workflowDisplayName);
            node.DisplayName = workflowDisplayName + ":" + GetDisplayNameSanitized(activity);
            return node;
        }

        static public Node CreateSimpleNodeFromTransition(Transition transition, string workflowDisplayName)
        {
            if (transition == null)
            {
                return null;
            }

            Node node = CreateEmptyNode(workflowDisplayName);
            node.DisplayName = workflowDisplayName + ":" + SanitizeString(transition.DisplayName);
            return node;
        }

        static public Node CreateEmptyNode(string workflowDisplayName, bool addWorkflowName = false)
        {
            Node node = new Node();
            node.DisplayName = "";
            node.Id = GetNextId(workflowDisplayName);
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

        static public string GetDisplayNameSanitized(State state)
        {
            if (state == null)
            {
                return "";
            }

            return SanitizeString(state.DisplayName);
        }

        static public string SanitizeString(string s)
        {
            return s.Replace(" ", "_");
        }

        public static bool IsFullPath(string path)
        {
            return !String.IsNullOrWhiteSpace(path)
                && path.IndexOfAny(System.IO.Path.GetInvalidPathChars().ToArray()) == -1
                && Path.IsPathRooted(path)
                && !Path.GetPathRoot(path).Equals(Path.DirectorySeparatorChar.ToString(), StringComparison.Ordinal);
        }

    }
}
