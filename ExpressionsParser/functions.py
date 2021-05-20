import myparser


def my_function(t,x):
    if x == "loan":
        return (myparser.TokenType.T_NUM,0)
    
    return (t,x)