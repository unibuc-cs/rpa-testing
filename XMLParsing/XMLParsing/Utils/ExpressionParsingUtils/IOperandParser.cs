namespace XMLParsing.Utils.ExpressionParsingUtils
{
    interface IOperandParser
    {
        void SetNext(IOperandParser operandParser);

        string Handle(object operand);
    }
}
