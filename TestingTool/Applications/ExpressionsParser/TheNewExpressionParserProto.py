
#================
import ast
import sys
class GenericCallparsing(ast.NodeVisitor):
    def __init__(self):
        self.attributesToCall = [] # The list of objects invoked up to the function call
        self.funcNames : [str] = [] # Name of the called function from the last attribute in the list above, or if empty it means it is a global function
        self.params = []

    def visit_Attribute(self, node):
        ast.NodeVisitor.generic_visit(self, node)
        self.attributesToCall.append(node.attr)

    def visit_Name(self, node):
        self.funcNames.append(node.id)

    def visit_Param(self, node):
        ast.NodeVisitor.generic_visit(self, node)
        self.params.append(node.id)


class ParseFunctionsVisitor(ast.NodeVisitor):
    def visit_Call(self, node):
        p = GenericCallparsing()
        p.visit(node.func)

        out_text = f"Attributes: {p.attributesToCall} | CallName = {p.funcNames} | Params = {p.params}"
        print(out_text)

        ast.NodeVisitor.generic_visit(self, node)

#================


if __name__ == '__main__':
    code = 'something = a.b.method(foo() + xtime.time(), var=1) + q.y(x.m())'
    tree = ast.parse(code)
    ParseFunctionsVisitor().visit(tree)

    sys.exit(0)
