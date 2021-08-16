using System;

namespace XMLParsing.Utils.ExpressionParsingUtils
{
    class CSharpValueParser : BaseOperandParser
    {
        public override string Handle(object operand)
        {
            string result = null;
            try
            {
                var res = ReflectionHelpers.CallMethod(operand, "get_Value");
                if (res != null)
                {
                    // 0 wrapped as object is casted to null string so we should avoid this.
                    var resAsString = res as string;
                    if (resAsString != null)
                    {
                        result = resAsString;
                    }
                    else
                    {
                        result = "0";
                    }
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
