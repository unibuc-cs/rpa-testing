using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;
using UiPath.Core.Activities;
using XMLParsing.Services.Parsers.ActivityParser;
using XMLParsing.Services.Parsers.NativeActivityParser;

namespace XMLParsing.Services
{
    class ActivityParserFactory
    {
        private static readonly Lazy<ActivityParserFactory> LazyInstance = new Lazy<ActivityParserFactory>(() => new ActivityParserFactory());

        private ActivityParserFactory()
        {
        }

        public static ActivityParserFactory Instance
        {
            get
            {
                return LazyInstance.Value;
            }
        }

        public IActivityParser GetParser(Activity activity)
        {
            if(activity == null)
            {
                return null;
            }

            var activityParserDict = new Dictionary<Type, Func<IActivityParser>>
            {
                { typeof(Flowchart), () => new FlowchartParser() },
                { typeof(Sequence), () => new SequenceParser() },
                { typeof(InvokeWorkflowFile), () => new InvokeWfActivityParser() },
                { typeof(Assign), () => new AssignActivityParser() },
                { typeof(If), () => new IfActivityParser() }
            };

            if (activityParserDict.ContainsKey(activity.GetType()))
            {
                return activityParserDict[activity.GetType()]();
            }
            else
            {
                return new DefaultActivityParser();
            }
        }
    }

}