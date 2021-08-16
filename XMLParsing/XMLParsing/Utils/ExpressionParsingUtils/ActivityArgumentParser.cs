using System;

namespace XMLParsing.Utils.ExpressionParsingUtils
{
    class ActivityArgumentParser : BaseOperandParser
    {
        public override string Handle(object operand)
        {
            string result = null;
            try
            {
                var expression = ReflectionHelpers.CallMethod(operand, "get_Expression");
                result = ReflectionHelpers.CallMethod(expression, "get_ExpressionText") as string;
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
