using System;

namespace XMLParsing.Utils
{
    class ExpressionUtils
    {
        public static string TryParseExpression(object operand)
        {
            string t1 = TryParseActivityArgument(operand);
            if(t1 != null)
            {
                return t1;
            }

            string t2 = TryParseActivityValue(operand);
            if (t2 != null)
            {
                return t2;
            }

            return "";
        }

        private static string TryParseActivityArgument(object operand)
        {
            try
            {
                var expression = ReflectionHelpers.CallMethod(operand, "get_Expression");
                return ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;
            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                return null;
            }
        }

        private static string TryParseActivityValue(object operand)
        {
            try
            {
                var expression = ReflectionHelpers.CallMethod(operand, "get_Expression");
                return ReflectionHelpers.CallMethod(expression, "get_Value").ToString();
            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                return null;
            }
        }
    }
}
