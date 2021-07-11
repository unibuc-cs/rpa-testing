namespace XMLParsing.Utils
{
    class AnnotationHelper
    {
        private static string VARIABLES_ANNOTATION = "@Variables";

        public static string TryExtractVariableAnnotation(string annotation)
        {
            if (annotation == null)
            {
                return null;
            }

            int startIndex = annotation.IndexOf(VARIABLES_ANNOTATION);
            
            if (startIndex == -1)
            {
                return null;
            }

            int jsonStartIndex = annotation.IndexOf("{", startIndex);
            int jsonEndIndex = annotation.LastIndexOf("}");

            return annotation.Substring(jsonStartIndex, jsonEndIndex - jsonStartIndex + 1);
        }
    }
}
