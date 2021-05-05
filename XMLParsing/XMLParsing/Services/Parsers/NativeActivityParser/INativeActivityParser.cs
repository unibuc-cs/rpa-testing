using XMLParsing.Common;
using System.Activities;

namespace XMLParsing.Services
{
    interface INativeActivityParser
    {

        void ParseNativeActivity(NativeActivity nativeActivity, Workflow workflow);

    }
}
