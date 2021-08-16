using System;

namespace XMLParsing.Utils.ExpressionParsingUtils
{
    class CSharpExpressionParser : BaseOperandParser
    {
        public override string Handle(object operand)
        {
            string result = null;
            try
            {
                result = ReflectionHelpers.CallMethod(operand, "get_ExpressionText") as string;
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
