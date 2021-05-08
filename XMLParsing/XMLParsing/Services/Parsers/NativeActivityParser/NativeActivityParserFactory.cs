using System;
using System.Activities;
using System.Activities.Statements;
using System.Collections.Generic;

namespace XMLParsing.Services
{
    class NativeActivityParserFactory
    {
        private static readonly Lazy<NativeActivityParserFactory> LazyInstance = new Lazy<NativeActivityParserFactory>(() => new NativeActivityParserFactory());

        private NativeActivityParserFactory()
        {
        }

        public static NativeActivityParserFactory Instance
        {
            get
            {
                return LazyInstance.Value;
            }
        }

        public INativeActivityParser GetParser(NativeActivity nativeActivity)
        {
            if(nativeActivity == null)
            {
                return null;
            }

            var activityParserDict = new Dictionary<Type, Func<INativeActivityParser>>
            {
                { typeof(Flowchart), () => new FlowchartParser() } 
            };

            if (activityParserDict.ContainsKey(nativeActivity.GetType()))
            {
                return activityParserDict[nativeActivity.GetType()]();
            }
            else
            {
                throw new System.NotImplementedException();
            }
        }
    }

}