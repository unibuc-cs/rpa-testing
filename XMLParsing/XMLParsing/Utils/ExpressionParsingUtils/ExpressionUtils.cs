using System;
using System.Collections.Generic;
using XMLParsing.Utils.ExpressionParsingUtils;

namespace XMLParsing.Utils
{
    class ExpressionUtils
    {
        static readonly IList<IOperandParser> operandParsers;

        static ExpressionUtils()
        {
            operandParsers = new List<IOperandParser>
            {
                new ActivityArgumentParser(),
                new ActivityValueParser(),
                new CSharpExpressionParser(),
                new CSharpValueParser(),
            };

            for (int i = 0; i < operandParsers.Count - 1; i++)
            {
                operandParsers[i].SetNext(operandParsers[i + 1]);
            }
        }

        public static string TryParseExpression(object operand)
        {
            return operandParsers[0].Handle(operand);
        }

    }
}
