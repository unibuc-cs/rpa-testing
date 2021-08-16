namespace XMLParsing.Utils.ExpressionParsingUtils
{
    class BaseOperandParser : IOperandParser
    {
        public IOperandParser nextHandler;

        public void SetNext(IOperandParser operandParser)
        {
            nextHandler = operandParser;
        }

        public virtual string Handle(object operand)
        {
            if (nextHandler != null)
            {
                return nextHandler.Handle(operand);
            }

            return "";
        }
    }
}
