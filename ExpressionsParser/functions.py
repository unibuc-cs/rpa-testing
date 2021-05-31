import myparser


def convert_object_with_function(t,x):
    # if x == "loan":
    #     return (myparser.TokenType.T_NUM,0)

    return (t,x)

def convert_not_implemented_object(c):
    if c == 'date(now)':
        return 1234
    raise Exception('Invalid token: {}'.format(c))
