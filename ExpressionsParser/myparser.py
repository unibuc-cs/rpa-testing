import enum
import re


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


class Node:
    def __init__(self, token_type, value=None):
        self.token_type = token_type
        self.value = value
        self.children = []


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
    
    while len(s) > 0: 
        c= ''
        while s[0] == ' ':
             s = s[1:]
        if s[0] == '(' or s[0] == ')':
            c = s[0]
            s = s[1:]
        else: 
          while len(s) > 0 and (s[0] != ' ' and s[0] != '(' and s[0] != ')'):
            c = c + s[0]
            s = s[1:]
    
        #print(c)
        #print(s)
        append=True
        if c in mappings:
            token_type = mappings[c]
            token = Node(token_type, value=operations[token_type])
        elif re.match(r'^[-+]?[0-9]+$', c):
            token = Node(TokenType.T_NUM, value=int(c))
        elif re.match(r'\s',c):
            append = False
        elif re.match(r'^\w+$', c):
            token = Node(TokenType.T_VAR, value=c)

        else:
            raise Exception('Invalid token: {}'.format(c))
       # print(append)
        if append: 
          #print(token.token_type)
          tokens.append(token)
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

    match(tokens, TokenType.T_LPAR)
    expression = parse_e(tokens)
    match(tokens, TokenType.T_RPAR)

    return expression


def parse(inputstring):
    tokens = lexical_analysis(inputstring)
    ast = parse_e(tokens)
    match(tokens, TokenType.T_END)
    return ast
