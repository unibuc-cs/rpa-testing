import sys
import operator
import myparser


operations = {
    myparser.TokenType.T_PLUS: operator.add,
    myparser.TokenType.T_MINUS: operator.sub,
    myparser.TokenType.T_MULT: operator.mul,
    myparser.TokenType.T_DIV: operator.truediv,
    myparser.TokenType.T_AND: operator.and_,
    myparser.TokenType.T_OR: operator.or_,
    myparser.TokenType.T_GT: operator.gt,
    myparser.TokenType.T_GTE: operator.ge,
    myparser.TokenType.T_LT: operator.lt,
    myparser.TokenType.T_LTE: operator.le,
    myparser.TokenType.T_EQ: operator.eq,
    myparser.TokenType.T_NEQ: operator.ne,
    
}
 
    
def compute(node):
    if node.token_type == myparser.TokenType.T_NUM:
        return node.value
    left_result = compute(node.children[0])
    right_result = compute(node.children[1])
    operation = operations[node.token_type]
    return operation(left_result, right_result)


if __name__ == '__main__':
    ast = myparser.parse(sys.argv[1])
    result = compute(ast)
    print(result)
