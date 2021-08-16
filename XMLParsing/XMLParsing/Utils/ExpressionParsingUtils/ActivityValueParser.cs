using System;

namespace XMLParsing.Utils.ExpressionParsingUtils
{
    class ActivityValueParser : BaseOperandParser
    {
        public override string Handle(object operand)
        {
            string result = null;
            try
            {
                var expression = ReflectionHelpers.CallMethod(operand, "get_Expression");
                result = ReflectionHelpers.CallMethod(expression, "get_Value").ToString();

                // Test string expression
                var expressionAct = expression as System.Activities.Activity<string>;
                if (expressionAct != null)
                {
                    // This means the expression is a string
                    result = "\"" + result + "\"";
                }
            }
            catch (Exception)
            {
            }

            if (result != null)
            {
                return result;
            }
            else
            {
                return base.Handle(operand);
            }
        }
    }
}
