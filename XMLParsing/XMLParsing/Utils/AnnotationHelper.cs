using System.Linq;

namespace XMLParsing.Utils
{
    class AnnotationHelper
    {
        private static string VARIABLES_ANNOTATION = "@Variables";
        private static string EXPRESSION_ANNOTATION = "@Expression";

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
            int jsonEndIndex = GetJsonEnd(annotation, jsonStartIndex);
            if(jsonEndIndex < jsonStartIndex)
            {
                return null;
            }

            return annotation.Substring(jsonStartIndex, jsonEndIndex - jsonStartIndex + 1);
        }

        public static string TryExtractExpressionAnnotation(string annotation)
        {
            if (annotation == null)
            {
                return null;
            }

            int startIndex = annotation.IndexOf(EXPRESSION_ANNOTATION);

            if (startIndex == -1)
            {
                return null;
            }

            int jsonStartIndex = annotation.IndexOf("{", startIndex);
            int jsonEndIndex = GetJsonEnd(annotation, jsonStartIndex);
            if (jsonEndIndex < jsonStartIndex)
            {
                return null;
            }

            return annotation.Substring(jsonStartIndex, jsonEndIndex - jsonStartIndex + 1);
        }

        // We are validating further in the code for the json structure
        // so here we need something simple that stops when the number of closed
        // brackets is equal to the one of opened brackets.
        private static int GetJsonEnd(string text, int startingIndex)
        {
            if(text == null || startingIndex < 0 || startingIndex > text.Length - 1)
            {
                return -1;
            }

            int opendBracketsCount = 1;
            int i = startingIndex + 1;
            char[] openBrackets = { '[', '{' };
            char[] closingBrackets = { ']', '}' };

            while(i < text.Length && opendBracketsCount != 0)
            {
                if(openBrackets.Contains(text[i]))
                {
                    opendBracketsCount++;
                }
                if(closingBrackets.Contains(text[i]))
                {
                    opendBracketsCount--;
                }
                i++;
            }

            if(opendBracketsCount != 0)
            {
                return -1;
            }

            return i - 1;
        }
    }
}
