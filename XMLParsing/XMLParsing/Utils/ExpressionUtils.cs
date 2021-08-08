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

            string t4 = TryParseCSharpExpression(operand);
            if (t4 != null)
            {
                return t4;
            }

            string t5 = TryParseCSharpValue(operand);
            if (t5 != null)
            {
                return t5;
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

        private static string TryParseCSharpExpression(object operand)
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

        private static string TryParseCSharpValue(object operand)
        {
            try
            {
                var res = ReflectionHelpers.CallMethod(operand, "get_Value");
                if (res == null)
                {
                    return null;
                } 
                else
                {
                    // 0 wrapped as object is casted to null string so we should avoid this.
                    var resAsString = res as string;
                    if (resAsString != null) 
                    {
                        return resAsString;
                    }

                    return "0";
                }
            }
            catch (Exception e)
            {
                // Console.WriteLine(e.Message);
                return null;
            }
        }
    }
}
