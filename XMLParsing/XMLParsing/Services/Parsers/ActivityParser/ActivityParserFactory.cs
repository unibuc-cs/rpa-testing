using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;
using UiPath.Core.Activities;
using UiPath.CSV.Activities;
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

            var activityParserDict = new Dictionary<String, Func<IActivityParser>>
            {
                { typeof(Flowchart).Name, () => new FlowchartParser() },
                { typeof(Sequence).Name, () => new SequenceParser() },
                { typeof(InvokeWorkflowFile).Name, () => new InvokeWfActivityParser() },
                { typeof(Assign).Name, () => new AssignActivityParser() },
                { typeof(If).Name, () => new IfActivityParser() },
                { typeof(ReadCsvFile).Name, () => new ReadCsvFileActivityParser() },
                { typeof(InterruptibleWhile).Name, () => new InterruptibleWhileActivityParser() },
                { typeof(InterruptibleDoWhile).Name, () => new InterruptibleDoWhileActivityParser() },
                { typeof(UiPath.Core.Activities.ForEach<>).Name, () => new ForEachActivityParser() },
                { typeof(ForEachRow).Name, () => new ForEachActivityParser() },
                { typeof(StateMachine).Name, () => new StateMachineActivityParser() }
            };

            if (activityParserDict.ContainsKey(activity.GetType().Name))
            {
                return activityParserDict[activity.GetType().Name]();
            }
            else
            {
                return new DefaultActivityParser();
            }
        }
    }

}