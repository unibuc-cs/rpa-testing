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

            string t3 = TryParseValue(operand);
            if (t3 != null)
            {
                return t3;
            }

            string t4 = TryParseCSharpValue(operand);
            if (t4 != null)
            {
                return t4;
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
                // Console.WriteLine(e.Message);
                return null;
            }
        }

        private static string TryParseActivityValue(object operand)
        {
            try
            {
                var expression = ReflectionHelpers.CallMethod(operand, "get_Expression");
                var res = ReflectionHelpers.CallMethod(expression, "get_Value").ToString();

                // Test string expression
                var expressionAct = expression as System.Activities.Activity<string>;
                if(expressionAct != null)
                {
                    // This means the expression is a string
                    res = "\"" + res + "\"";
                }

                return res;
            }
            catch (Exception e)
            {
                // Console.WriteLine(e.Message);
                return null;
            }
        }

        private static string TryParseValue(object operand)
        {
            try
            {
                var expression = ReflectionHelpers.CallMethod(operand, "get_Expression");
                return ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;
            }
            catch (Exception e)
            {
                // Console.WriteLine(e.Message);
                return null;
            }
        }

        private static string TryParseCSharpValue(object operand)
        {
            try
            {
                return ReflectionHelpers.CallMethod(operand, "get_ExpressionText") as string;
            }
            catch (Exception e)
            {
                // Console.WriteLine(e.Message);
                return null;
            }
        }
    }
}
