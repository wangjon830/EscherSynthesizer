from collections import deque

# Program structs
ITE = "ITE"

# Synthesis Structs
NUM = "NUM"
INTVAR = "INTVAR"
LISTVAR = "LISTVAR"
SELF = "SELF"

# Sythesis Boolean Ops
FALSE_exp = "FALSE"
TRUE_exp = "TRUE"
AND = "AND"
OR = "OR"
NOT = "NOT"
EQUAL = "EQUAL"
ISEMPTY = "ISEMPTY"
ISNEGATIVE = "ISNEGATIVE"
LT = "LT"

# Synthesis Int Ops
PLUS = "PLUS"
MINUS = "MINUS"
TIMES = "TIMES"
INCNUM = "INCNUM"
DECNUM = "DECNUM"
NEG = "NEG"
DIV2 = "DIV2"
ZERO = "ZERO"

# Syntheis List Ops
HEAD = "HEAD"
TAIL = "TAIL"
INCLIST = "INCLIST"
DECLIST = "DECLIST"
CONS = "CONS"
CONCAT = "CONCAT"
EMPTYLIST = "EMPTYLIST"
ZEROLIST = "ZEROLIST"

varsAndConst = [INTVAR, LISTVAR, NUM]

boolOps = [FALSE_exp, TRUE_exp, AND, OR, NOT, EQUAL, ISEMPTY, ISNEGATIVE, LT]
intOps = [INTVAR, NUM, PLUS, MINUS, TIMES, INCNUM, DECNUM, NEG, DIV2, ZERO, HEAD]
listOps = [LISTVAR, TAIL, CONS, CONCAT, INCLIST, DECLIST, EMPTYLIST, ZEROLIST]

noArgOps = [ZERO, EMPTYLIST]
oneArgOps = [NOT, ISEMPTY, ISNEGATIVE, INCNUM, DECNUM, NEG, DIV2, HEAD, TAIL, INCLIST, DECLIST, ZEROLIST]
twoArgOps = [AND, OR, EQUAL, LT, PLUS, MINUS, TIMES, CONS, CONCAT]

class Error(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message


# *************************************************
# ***********  AST node definitions ***************
# *************************************************

class Node:
    def __init__(self):
        self.inputoutputs = []

    def memoize(self, input, output):
        self.inputoutputs.append([input,output])

    def checkMem(self, input):
        for inputoutput in self.inputoutputs:
            if(inputoutput[0] == input):
                return inputoutput[1]
        return None
            
    def __str__(self):
        raise Error("Unimplemented method: str()")

    def interpret(self):
        raise Error("Unimplemented method: interpret()")

class FalseExp(Node):
    def __init__(self):
        super().__init__()
        self.type = FALSE_exp

    def __str__(self):
        return "false"

    def interpret(self, envt):
        return False

class TrueExp(Node):
    def __init__(self):
        super().__init__()
        self.type = TRUE_exp

    def __str__(self):
        return "true"

    def interpret(self, envt):
        return True

class IntVar(Node):
    def __init__(self, name):
        super().__init__()
        self.type = INTVAR
        self.val = name

    def __str__(self):
        return self.val

    def interpret(self, envt):
        return envt[self.val]

class ListVar(Node):
    def __init__(self, name):
        super().__init__()
        self.type = LISTVAR
        self.val = name

    def __str__(self):
        return self.val

    def interpret(self, envt):
        return envt[self.val]

class Num(Node):
    def __init__(self, val):
        super().__init__()
        self.type = NUM
        self.val = val

    def __str__(self):
        return str(self.val)

    def interpret(self, envt):
        return self.val

class Self(Node):
    def __init__(self, val, args):
        super().__init__()
        self.type = NUM
        self.left = val
        self.right = args

    def __str__(self):
        right = "["
        for prog in self.right:
            right += str(prog)
            right += ", "
        right += "]"
        return "(" + str(self.left.__name__) + "(" + right + "))"

    def interpret(self, envt):
        args = []
        for prog in self.right:
            if(prog.interpret(envt) == "ERROR"): return "ERROR"
            args.append(prog.interpret(envt))

        self.memoize(envt, self.left(args))
        return self.left(args)

class Zero(Node):
    def __init__(self):
        super().__init__()
        self.type = ZERO
        self.val = 0

    def __str__(self):
        return str(self.val)
    
    def interpret(self, envt):
        return 0

class ZeroList(Node):
    def __init__(self, size):
        super().__init__()
        self.type = ZEROLIST
        self.val = size

    def __str__(self):
        ret = '(ZeroList(' + str(self.val) + '))'
        return ret

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        
        if(self.val.interpret(envt) != "ERROR"):
            ret = []
            for x in range(0, int(self.val.interpret(envt))):
                ret.append(0)

            self.memoize(envt, ret)
            return ret
        else:
            return "ERROR"

class Plus(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = PLUS
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "+" + str(self.right) +")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) + self.right.interpret(envt))
            return self.left.interpret(envt) + self.right.interpret(envt)
        else:
            return "ERROR"

class Minus(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = MINUS
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "-" + str(self.right) +")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) - self.right.interpret(envt))
            return self.left.interpret(envt) - self.right.interpret(envt)
        else:
            return "ERROR"

class Times(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = TIMES
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "*" + str(self.right) + ")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) * self.right.interpret(envt))
            return self.left.interpret(envt) * self.right.interpret(envt)
        else:
            return "ERROR"

class Lt(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = LT
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "<" + str(self.right) + ")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) < self.right.interpret(envt))
            return self.left.interpret(envt) < self.right.interpret(envt)
        else:
            return "ERROR"

class And(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = AND
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "&&" + str(self.right) + ")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) and self.right.interpret(envt))
            return self.left.interpret(envt) and self.right.interpret(envt)
        else:
            return "ERROR"

class Or(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = OR
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "||" + str(self.right) + ")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) or self.right.interpret(envt))
            return self.left.interpret(envt) or self.right.interpret(envt)
        else:
            return "ERROR"

class Not(Node):
    def __init__(self, left):
        super().__init__()
        self.type = NOT
        self.val = left

    def __str__(self):
        return "(!" + str(self.val)+ ")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            self.memoize(envt, not self.val.interpret(envt))
            return not self.val.interpret(envt)
        else:
            return "ERROR"

class Equals(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = EQUAL
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + " == " + str(self.right) +")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            self.memoize(envt, self.left.interpret(envt) == self.right.interpret(envt))
            return self.left.interpret(envt) == self.right.interpret(envt)
        else:
            return "ERROR"
        

class IsNegative(Node):
    def __init__(self, val):
        super().__init__()
        self.type = ISNEGATIVE
        self.val = val

    def __str__(self):
        return "(" + str(self.val) +" < 0)"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            self.memoize(envt, self.val.interpret(envt) < 0)
            return self.val.interpret(envt) < 0
        else:
            return "ERROR"

class Neg(Node):
    def __init__(self, val):
        super().__init__()
        self.type = NEG
        self.val = val

    def __str__(self):
        return "(-" + str(self.val) +")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            self.memoize(envt, self.val.interpret(envt)*-1)
            return self.val.interpret(envt)*-1
        else:
            return "ERROR"
        

class Div2(Node):
    def __init__(self, val):
        super().__init__()
        self.type = DIV2
        self.val = val

    def __str__(self):
        return "(" + str(self.val) +"/2)"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            self.memoize(envt, self.val.interpret(envt)/2)
            return self.val.interpret(envt)/2
        else:
            return "ERROR"
        

class IsEmpty(Node):
    def __init__(self, list):
        super().__init__()
        self.type = ISEMPTY
        self.val = list

    def __str__(self):
        return "(isEmpty(" + str(self.val)+ "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            self.memoize(envt, len(self.val.interpret(envt)) == 0)
            return len(self.val.interpret(envt)) == 0
        else:
            return "ERROR"
        
class Ite(Node):
    def __init__(self, c, t, f):
        super().__init__()
        self.type = ITE
        self.cond = c
        self.tcase = t
        self.fcase = f

    def __str__(self):
        return "(if " + str(self.cond) + " then " + str(self.tcase) + " else " + str(self.fcase) + ")"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.cond.interpret(envt) != "ERROR" and self.tcase.interpret(envt) != "ERROR" and self.fcase.interpret(envt) != "ERROR"):
            if (self.cond.interpret(envt)):
                self.memoize(envt, self.tcase.interpret(envt))
                return self.tcase.interpret(envt)
            else:
                self.memoize(envt, self.fcase.interpret(envt))
                return self.fcase.interpret(envt)
        else:
            return "ERROR"



class IncrementList(Node):
    def __init__(self, val):
        super().__init__()
        self.type = INCLIST
        self.val = val

    def __str__(self):
        return "(incrementlist(" + str(self.val) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) == "ERROR"):
            return "ERROR"

        ret = []
        for x in self.val.interpret(envt):
            if(x == "ERROR"): return "ERROR"
            if(isinstance(x, str)):
                print(x)
            else:
                ret.append(x + 1)
        self.memoize(envt, ret)
        return ret

class IncrementNum(Node):
    def __init__(self, val):
        super().__init__()
        self.type = INCNUM
        self.val = val

    def __str__(self):
        return "(incrementnum(" + str(self.val) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            ret = self.val.interpret(envt)+1
            self.memoize(envt, ret)
            return ret       
        else:
            return "ERROR"

class DecrementList(Node):
    def __init__(self, val):
        super().__init__()
        self.type = DECLIST
        self.val = val

    def __str__(self):
        return "(decrementlist(" + str(self.val) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) == "ERROR"):
            return "ERROR"

        ret = []
        for x in self.val.interpret(envt):
            if(x == "ERROR"): return "ERROR"
            ret.append(x - 1)
        self.memoize(envt, ret)
        return ret

class DecrementNum(Node):
    def __init__(self, val):
        super().__init__()
        self.type = DECNUM
        self.val = val

    def __str__(self):
        return "(decrementnum(" + str(self.val) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR"):
            ret = self.val.interpret(envt)-1
            self.memoize(envt, ret)
            return ret
        else:
            return "ERROR"


class EmptyList(Node):
    def __init__(self):
        super().__init__()
        self.type = EMPTYLIST
        self.val = []

    def __str__(self):
        return "[]"

    def interpret(self, envt):
        return []

class Cons(Node):
    def __init__(self, left, right):
        super().__init__()
        self.type = CONCAT
        self.left = left
        self.right = right

    def __str__(self):
        return "(cons(" + str(self.left) + ',' + str(self.right) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            ret = []
            ret.append(self.left.interpret(envt))

            if(self.right.type in intOps or self.right.type in boolOps):
                ret.append(self.right.interpret(envt))
            elif(self.right.type in listOps):
                ret += self.right.interpret(envt)
            self.memoize(envt, ret)
            return ret
        else:
            return "ERROR"

class Concat(Node):
    def __init__(self, list1, list2):
        super().__init__()
        self.type = CONCAT
        self.left = list1
        self.right = list2

    def __str__(self):
        return "(concat(" + str(self.left) + ',' + str(self.right) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.left.interpret(envt) != "ERROR" and self.right.interpret(envt) != "ERROR"):
            ret = []
            ret += self.left.interpret(envt)
            ret += self.right.interpret(envt)
            self.memoize(envt, ret)
            return ret
        else:
            return "ERROR"

class Head(Node):
    def __init__(self, list):
        super().__init__()
        self.type = HEAD
        self.val = list

    def __str__(self):
        return "(head(" + str(self.val) + "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR" and len(self.val.interpret(envt)) > 0):
            self.memoize(envt, self.val.interpret(envt)[0])
            return self.val.interpret(envt)[0]
        else:
            return "ERROR"

class Tail(Node):
    def __init__(self, list):
        super().__init__()
        self.type = TAIL
        self.val = list

    def __str__(self):
        return "(tail(" + str(self.val) + "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)
        if(self.val.interpret(envt) != "ERROR" and len(self.val.interpret(envt)) > 0):
            self.memoize(envt, self.val.interpret(envt)[1:])
            return self.val.interpret(envt)[1:]
        else:
            return "ERROR"

def isCorrect(program, inputoutputs):
    count = 0
    for i, inputoutput in enumerate(inputoutputs):
        out = program.interpret(inputoutput)
        #print (f'{i+1}. Evaluating programs {program}\non inputoutput examples {inputoutput}. The output of the program is {out}\n')
        if (out == inputoutput["_out"]):
            count += 1
        else:
            break
    return (len(inputoutputs) == count)
