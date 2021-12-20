import sys

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
ISPOSITIVE = "ISPOSITIVE"
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
        self.inputoutputs = {}

    def memoize(self, input, output):
        #if(self.inputoutputs != None):
        #    self.inputoutputs[str(input)] = output
        return

    def checkMem(self, input):
        #if(self.inputoutputs != None):
        #   if(str(input) in self.inputoutputs.keys()):
        #        return self.inputoutputs[str(input)]
        return None
            
    def __str__(self):
        raise Error("Unimplemented method: str()")

    def __hash__(self):
        return hash(str(self))

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
        
        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = []
            for x in range(0, int(val)):
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = left + right
            self.memoize(envt, ret)
            return ret
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = left-right
            self.memoize(envt, ret)
            return ret
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
            
        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = left*right
            self.memoize(envt, ret)
            return ret
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = left < right
            self.memoize(envt, ret)
            return ret
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = left and right
            self.memoize(envt, ret)
            return ret
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = left or right
            self.memoize(envt, ret)
            return ret
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
        
        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = not val
            self.memoize(envt, ret)
            return ret
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt) 
        if(left != "ERROR" and right != "ERROR"):
            ret = left == right
            self.memoize(envt, ret)
            return ret
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

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = val < 0
            self.memoize(envt, ret)
            return ret
        else:
            return "ERROR"

class IsPositive(Node):
    def __init__(self, val):
        super().__init__()
        self.type = ISPOSITIVE
        self.val = val

    def __str__(self):
        return "(" + str(self.val) +" >= 0)"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = val >= 0
            self.memoize(envt, ret)
            return ret
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

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = val*-1
            self.memoize(envt, ret)
            return ret
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

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = val/2
            self.memoize(envt, ret)
            return ret
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

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = len(val) == 0
            self.memoize(envt, ret)
            return ret
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

        cond = self.cond.interpret(envt)
        tcase = self.tcase.interpret(envt)
        fcase = self.fcase.interpret(envt)
        if(cond != "ERROR"):
            if (cond):
                if(tcase == "ERROR"): return "ERROR"
                ret = tcase
                self.memoize(envt, ret)
                return ret
            else:
                if(fcase == "ERROR"): return "ERROR"
                ret = fcase
                self.memoize(envt, ret)
                return ret
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

        val = self.val.interpret(envt)
        if(val == "ERROR"):
            return "ERROR"

        ret = []
        for x in val:
            if(x == "ERROR"): return "ERROR"
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

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = val+1
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

        val = self.val.interpret(envt)
        if(val == "ERROR"):
            return "ERROR"

        ret = []
        for x in val:
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

        val = self.val.interpret(envt)
        if(val != "ERROR"):
            ret = val-1
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
        self.type = CONS
        self.left = left
        self.right = right

    def __str__(self):
        return "(cons(" + str(self.left) + ',' + str(self.right) +  "))"

    def interpret(self, envt):
        if(self.checkMem(envt) != None):
            return self.checkMem(envt)

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = []
            ret.append(left)

            if(isinstance(right, list)):
                ret += (right)
            else:
                ret.append(right)
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

        left = self.left.interpret(envt)
        right = self.right.interpret(envt)
        if(left != "ERROR" and right != "ERROR"):
            ret = []
            ret += left
            ret += right
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

        val = self.val.interpret(envt)
        if(val != "ERROR" and len(val) > 0):
            ret = val[0]
            self.memoize(envt, ret)
            return ret
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

        val = self.val.interpret(envt)
        if(val != "ERROR" and len(val) > 0):
            ret = val[1:]
            self.memoize(envt, ret)
            return ret
        else:
            return "ERROR"

class Self(Node):
    def __init__(self, val, args):
        super().__init__()
        self.type = SELF
        self.left = val
        self.right = args

    def __str__(self):
        right = "["
        for prog in self.right:
            right += str(prog)
            right += ", "
        right += "]"
        return "(" + str(self.left["fun"].__name__) + "(" + right + "))"

    def interpret(self, envt):
        args = []

        for prog in self.right:
            if(prog.interpret(envt) == "ERROR"): return "ERROR"
            args.append(prog.interpret(envt))

        ret = self.left["fun"](args)
        self.memoize(envt, ret)
        return ret

def getOutput(program, inputoutputs):
    out_vect = []
    bool_vect = []
    for inputoutput in inputoutputs:
        out = program.interpret(inputoutput)
        out_vect.append(out)
        bool_vect.append(type(out) == type(inputoutput['_out']) and out == inputoutput['_out'])
    return [out_vect, bool_vect]

def getRecursiveCall(program):
    if(isinstance(program, Self)):
        return program
        
    for key in program.__dict__:
        if(isinstance(program.__dict__[key], Self)):
            return program.__dict__[key]
        elif(isinstance(program.__dict__[key], Node)):
            rec = getRecursiveCall(program.__dict__[key])
            if(isinstance(rec, Self)):
                return rec
    return None

def getSatAndTest(program, recursiveCall, input, oracleInfo, depth, thresh):
    new_input_dict = {}
    new_input_arr = []
    for i, var in enumerate(recursiveCall.right):
        # Base case handling
        ret = var.interpret(input)
        if(ret == 'ERROR'):
            return True
        if(isinstance(ret, int) and ret <= 0):
            return True
        if(depth >= thresh or (isinstance(ret, int) and ret > 1000000)):
            return False
        new_input_dict[list(input.keys())[i]] = ret
        new_input_arr.append(ret)
    if(oracleInfo['fun'](new_input_arr) != program.interpret(new_input_dict)):
        return False
    return True and getSatAndTest(program, recursiveCall, new_input_dict, oracleInfo, depth+1, thresh)

def testRecurse(program, inputoutputs, oracleInfo):
    rec = getRecursiveCall(program)
    if(rec == None):
        return False
    for input in inputoutputs:
        if(input['_out'] != program.interpret(input)):
            return False
        if not getSatAndTest(program, rec, input, oracleInfo, 0, 10):
            return False
        
    return True

def isTerminating(program, inputoutputs, oracleInfo):
    rec = getRecursiveCall(program)
    if(rec == None):
        return True
    for input in inputoutputs:
        if not getSat(program, rec, input, oracleInfo, 0, 10):
            return False
    return True

def getSat(program, recursiveCall, input, oracleInfo, depth, thresh):
    new_input_dict = {}
    for i, var in enumerate(recursiveCall.right):
        # Base case handling
        ret = var.interpret(input)
        if(ret == 'ERROR'):
            return True
        if(isinstance(ret, int) and ret <= 0):
            return True
        if(depth >= thresh):
            return False
        new_input_dict[list(input.keys())[i]] = ret
    return True and getSat(program, recursiveCall, new_input_dict, oracleInfo, depth+1, thresh)

def isCorrect(program, inputoutputs):
    count = 0
    for i, inputoutput in enumerate(inputoutputs):
        out = program.interpret(inputoutput)

        if (out == inputoutput["_out"]):
            count += 1
        else:
            break
    return (len(inputoutputs) == count)
