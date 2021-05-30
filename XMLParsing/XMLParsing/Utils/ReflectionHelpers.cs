using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;

namespace XMLParsing.Utils
{
    class ReflectionHelpers
    {
        public static object CallMethod(object source, string name)
        {
            return CallMethod(source, name, new object[] { });
        }

        public static object CallMethod(object source, string name, object[] parameters)
        {
            if(source == null)
            {
                return null;
            }

            try
            {
                MethodInfo methodInfo = source.GetType().GetMethod(name);
                return methodInfo.Invoke(source, parameters);
            }
            catch (Exception e)
            {
                // Console.WriteLine(e.Message);
            }

            return null;
        }

    }
}
