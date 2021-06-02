import enum
import re
import functions


class TokenType(enum.Enum):
    T_NUM = 0
    T_PLUS = 1
    T_MINUS = 2
    T_MULT = 3
    T_DIV = 4
    T_LPAR = 5
    T_RPAR = 6
    T_END = 7
    T_AND = 8
    T_OR = 9
    T_GT = 10 
    T_GTE = 11
    T_LT = 12
    T_LTE = 13
    T_EQ = 14
    T_NEQ = 15
    T_VAR = 16
    T_NOT = 17
    T_BOOL = 18,
    T_STRING = 19


class Node:
    def __init__(self, token_type, value=None):
        self.token_type = token_type
        self.value = value
        self.children = []

def convert_object_with_function(t,c):
    return functions.convert_object_with_function(t,c)

def convert_not_implemented_object(c):
    return functions.convert_not_implemented_object(c)

def lexical_analysis(s):
    mappings = {
        '+': TokenType.T_PLUS,
        '-': TokenType.T_MINUS,
        '*': TokenType.T_MULT,
        '/': TokenType.T_DIV,
        '(': TokenType.T_LPAR,
        ')': TokenType.T_RPAR,
        'AND': TokenType.T_AND,
        'OR': TokenType.T_OR,
        'and': TokenType.T_AND,
        'or': TokenType.T_OR,
        '>': TokenType.T_GT,
        '>=': TokenType.T_GTE,
        '>==': TokenType.T_GTE,
        '<': TokenType.T_LT,
        '<=': TokenType.T_LTE,
        '=': TokenType.T_EQ,
        '==': TokenType.T_EQ,
        '!=': TokenType.T_NEQ,
        '!': TokenType.T_NOT
        }
    operations ={
        TokenType.T_PLUS: '+',
        TokenType.T_MINUS:'-',
        TokenType.T_MULT:'*',
        TokenType.T_DIV:'/',
        TokenType.T_LPAR:'(',
        TokenType.T_RPAR:')',
        TokenType.T_AND: 'And',
        TokenType.T_OR: 'Or',
        TokenType.T_GT: '>',
        TokenType.T_GTE:'>=',
        TokenType.T_LT:'<',
        TokenType.T_LTE: '<=',
        TokenType.T_EQ : '==',
        TokenType.T_NEQ: '!=',
        TokenType.T_NOT: 'Not'
        }
    tokens = []
    #split_tokens = s.split(' ')
    #print(split_tokens)
    #for c in split_tokens:
    s = s.strip()
    while len(s) > 0: 
        c= ''
        while s[0] == ' ':
             s = s[1:]
        if s[0] == '(' or s[0] == ')':
            c = s[0]
            s = s[1:]
        elif s[0] == '\"':
            s = s[1:]
            c = '\"'+s[0:(s.rfind('\"')+1)]
            s= s[(s.rfind('\"')+1):]
        elif s.startswith('True'): 
            c = 'True'
            s = s[4:]
        elif s.startswith('False'):
            c = 'False'
            s = s[5:]
        else: 
          while len(s) > 0 and (s[0] != ' ' and s[0] != '(' and s[0] != ')'):
              # TODO change this to acccept function calls
            c = c + s[0]
            s = s[1:]
    
        #print(c)
        #print(s)
        append=True
        if c in mappings:
            token_type = mappings[c]
            token = Node(token_type, value=operations[token_type])
        elif c == 'True' or c == 'False':
            (t,c1)=convert_object_with_function(TokenType.T_BOOL,c)
            token = Node(t,value=c1)
        elif c == 'true':
            (t, c1) = convert_object_with_function(TokenType.T_BOOL, 'True')
            token = Node(t, value=c1)
        elif c == 'false':
            (t, c1) = convert_object_with_function(TokenType.T_BOOL, 'False')
            token = Node(t, value=c1)
        elif c[0]=='\"':
             (t,c1) = convert_object_with_function(TokenType.T_STRING,c)
             token = Node(t, value=c1)
        elif re.match(r'^[-+]?[0-9]+$', c):
            (t,c1) = convert_object_with_function(TokenType.T_NUM,int(c))
            token = Node(t, value=c1)
        elif re.match(r'\s',c):
            append = False
        elif re.match(r'^\w+$', c) :
            # TO DO check if var appears in the list of vars
            (t,c1) = convert_object_with_function(TokenType.T_VAR,c)
            token = Node(t, value=c1)

        else:
            c1 = convert_not_implemented_object(c)


       # print(append)
        if append: 
          #print(token.token_type)
          tokens.append(token)
        s = s.strip()
    tokens.append(Node(TokenType.T_END))
  
    return tokens


def match(tokens, token):
    if tokens[0].token_type == token:
        return tokens.pop(0)
    else:
        raise Exception('Invalid syntax on token {}'.format(tokens[0].token_type))




def parse_e(tokens):
    left_node = parse_e0(tokens)

    while tokens[0].token_type in [TokenType.T_AND, TokenType.T_OR]:
        node = tokens.pop(0)
        node.children.append(left_node)
        node.children.append(parse_e0(tokens))
        left_node = node

    return left_node


def parse_e0(tokens):
    left_node = parse_e1(tokens)

    while tokens[0].token_type in [TokenType.T_GT, TokenType.T_GTE, TokenType.T_LT, TokenType.T_LTE, TokenType.T_EQ, TokenType.T_NEQ]:
        node = tokens.pop(0)
        node.children.append(left_node)
        node.children.append(parse_e1(tokens))
        left_node = node

    return left_node


def parse_e1(tokens):
    left_node = parse_e2(tokens)

    while tokens[0].token_type in [TokenType.T_PLUS, TokenType.T_MINUS]:
        node = tokens.pop(0)
        node.children.append(left_node)
        node.children.append(parse_e2(tokens))
        left_node = node

    return left_node


def parse_e2(tokens):
    left_node = parse_e3(tokens)

    while tokens[0].token_type in [TokenType.T_MULT, TokenType.T_DIV]:
        node = tokens.pop(0)
        node.children.append(left_node)
        node.children.append(parse_e3(tokens))
        left_node = node

    return left_node


def parse_e3(tokens):
    if tokens[0].token_type == TokenType.T_NUM:
        return tokens.pop(0)
    if tokens[0].token_type == TokenType.T_VAR:
        return tokens.pop(0)
    if tokens[0].token_type == TokenType.T_STRING:
        return tokens.pop(0)
    if tokens[0].token_type == TokenType.T_BOOL:
        return tokens.pop(0)
    match(tokens, TokenType.T_LPAR)
    expression = parse_e(tokens)
    match(tokens, TokenType.T_RPAR)

    return expression


def parse(inputstring):
    tokens = lexical_analysis(inputstring)
    ast = parse_e(tokens)
    match(tokens, TokenType.T_END)
    return ast
