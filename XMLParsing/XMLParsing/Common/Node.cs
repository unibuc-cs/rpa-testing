namespace XMLParsing.Common
{
    class Node
    {
        public int Id { get; set; }
        public string DisplayName { get; set; }

        public bool IsConditional { get; set; }

        public string Expression { get; set; }

        public Node() 
        {
        }
    }
}
