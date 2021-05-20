namespace XMLParsing.Common
{
    class Transition
    {
        public static string TRUE_TRANSITION_VALUE = "True";
        public static string FALSE_TRANSITION_VALUE = "False";

        public Node Source { get; set; }
        public Node Destination { get; set; }
        public string Expression { get; set; }
        public string ExpressionValue { get; set; }
    }
}
