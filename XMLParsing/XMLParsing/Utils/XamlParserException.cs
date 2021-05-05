using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace XMLParsing.Utils
{
    class XamlParserException : Exception
    {
        public XamlParserException(string exceptionMessage) : base(exceptionMessage)
        {
        }

    }
}
