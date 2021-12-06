from collections import deque

# Synthesis Structs
NUM = "NUM"
VAR = "VAR"
LIST = "LIST"

# Sythesis Boolean Ops
FALSE_exp = "FALSE"
AND = "AND"
OR = "OR"
NOT = "NOT"
ITE = "ITE"

# Synthesis Int Ops
PLUS = "PLUS"
TIMES = "TIMES"
LT = "LT"

# Syntheis List Ops
LENGTH = "LENGTH"
REVERSE = "REVERSE"
SORT = "SORT"
TAIL = "TAIL"
HEAD = "HEAD"
MAX = "MAX"
MIN = "MIN"
LSHIFT = "LSHIFT"
RSHIFT = "RSHIFT"
INCREMENT = "INCREMENT"
MULTIPLYLIST = "MULTIPLYLIST"
EMPTY = "EMPTY"
CONCAT = "CONCAT"

ALLOPS = [NUM, FALSE_exp, VAR, LIST, PLUS, TIMES, LT, AND, OR, NOT, ITE, LENGTH, REVERSE, SORT, TAIL, HEAD, MAX, MIN, LSHIFT, RSHIFT, INCREMENT, MULTIPLYLIST, EMPTY, CONCAT]

class Error(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message


# *************************************************
# ***********  AST node definitions ***************
# *************************************************

class Node:
    def __str__(self):
        raise Error("Unimplemented method: str()")

    def interpret(self):
        raise Error("Unimplemented method: interpret()")

class FalseExp(Node):
    def __init__(self):
        self.type = FALSE_exp

    def __str__(self):
        return "false"

    def interpret(self, envt):
        return False

class Var(Node):
    def __init__(self, name):
        self.type = VAR
        self.name = name

    def __str__(self):
        return self.name

    def interpret(self, envt):
        return envt[self.name]

class Num(Node):
    def __init__(self, val):
        self.type = NUM
        self.val = val

    def __str__(self):
        return str(self.val)

    def interpret(self, envt):
        return self.val

class List(Node):
    def __init__(self, list):
        self.type = LIST
        self.list = []
        for x in list:
            if(isinstance(x, int)):
                self.list.append(Num(x))
            else:
                raise Error("Invalid List Element Type")

    def __str__(self):
        ret = '['
        for x in self.list:
            ret += str(x)
            ret += ', '
        ret += "]"
        return ret

    def interpret(self, envt):
        ret = []
        for x in self.list:
            ret.append(x.interpret(envt))
        return ret

class ZeroList(Node):
    def __init__(self, size):
        self.type = LIST
        self.list = []
        for x in range(0, size):
            self.list.append(Num(0))

    def __str__(self):
        ret = '['
        for x in self.list:
            ret += str(x)
            ret += ', '
        ret += "]"
        return ret

    def interpret(self, envt):
        ret = []
        for x in self.list:
            ret.append(x.interpret(envt))
        return ret

class Plus(Node):
    def __init__(self, left, right):
        self.type = PLUS
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "+" + str(self.right) +")"

    def interpret(self, envt):
        return self.left.interpret(envt) + self.right.interpret(envt)

class Times(Node):
    def __init__(self, left, right):
        self.type = TIMES
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "*" + str(self.right) + ")"

    def interpret(self, envt):
        return self.left.interpret(envt) * self.right.interpret(envt)

class Lt(Node):
    def __init__(self, left, right):
        self.type = LT
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "<" + str(self.right) + ")"

    def interpret(self, envt):
        return self.left.interpret(envt) < self.right.interpret(envt)

class And(Node):
    def __init__(self, left, right):
        self.type = AND
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "&&" + str(self.right) + ")"

    def interpret(self, envt):
        return self.left.interpret(envt) and self.right.interpret(envt)

class Or(Node):
    def __init__(self, left, right):
        self.type = OR
        self.left = left
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + "||" + str(self.right) + ")"

    def interpret(self, envt):
        return self.left.interpret(envt) or self.right.interpret(envt)

class Not(Node):
    def __init__(self, left):
        self.type = NOT
        self.left = left

    def __str__(self):
        return "(!" + str(self.left)+ ")"

    def interpret(self, envt):
        return not self.left.interpret(envt)

class Ite(Node):
    def __init__(self, c, t, f):
        self.type = ITE
        self.cond = c
        self.tcase = t
        self.fcase = f

    def __str__(self):
        return "(if " + str(self.cond) + " then " + str(self.tcase) + " else " + str(self.fcase) + ")"

    def interpret(self, envt):
        if (self.cond.interpret(envt)):
            return self.tcase.interpret(envt)
        else:
            return self.fcase.interpret(envt)

class Length(Node):
    def __init__(self, list):
        self.type = LENGTH
        self.list = list

    def __str__(self):
        return "(len(" + str(self.list) + "))"

    def interpret(self, envt):
        return len(self.list)

class Reverse(Node):
    def __init__(self, list):
        self.type = REVERSE
        self.list = list

    def __str__(self):
        return "(reverse(" + str(self.list) + "))"

    def interpret(self, envt):
        ret = []
        for x in self.list.reverse():
            ret.append(x.interpret(envt))
        return ret

class Sort(Node):
    def __init__(self, list):
        self.type = SORT
        self.list = list

    def __str__(self):
        return "(sort(" + str(self.list) + "))"

    def interpret(self, envt):
        ret = []
        for x in sorted(self.list, key = lambda x: x.val):
            ret.append(x.interpret(envt))
        return ret

class Head(Node):
    def __init__(self, list):
        self.type = HEAD
        self.list = list

    def __str__(self):
        return "(head(" + str(self.list) + "))"

    def interpret(self, envt):
        if(len(self.list) > 0):
            return self.list[0].interpret(envt)
        else:
            return FALSE_exp

class Tail(Node):
    def __init__(self, list):
        self.type = TAIL
        self.list = list

    def __str__(self):
        return "(tail(" + str(self.list) + "))"

    def interpret(self, envt):
        if(len(self.list) > 0):
            return self.list[-1].interpret(envt)
        else:
            return FALSE_exp

class Max(Node):
    def __init__(self, list):
        self.type = MAX
        self.list = list

    def __str__(self):
        return "(max(" + str(self.list) + "))"

    def interpret(self, envt):
        if(len(self.list) > 0):
            return max(self.list, key = lambda x: x.val).interpret(envt)
        else:
            return FALSE_exp

class Min(Node):
    def __init__(self, list):
        self.type = MIN
        self.list = list

    def __str__(self):
        return "(min(" + str(self.list) + "))"

    def interpret(self, envt):
        if(len(self.list) > 0):
            return min(self.list, key = lambda x: x.val).interpret(envt)
        else:
            return FALSE_exp

class Lshift(Node):
    def __init__(self, list, pos):
        self.type = LSHIFT
        self.list = list
        self.pos = pos

    def __str__(self):
        return "(lshift(" + str(self.list) + ',' + str(self.pos) +  "))"

    def interpret(self, envt):
        temp = deque(self.list)
        temp.rotate(-self.pos)
        ret = []
        for x in temp:
            ret.append(x.interpret(envt))
        return ret

class Rshift(Node):
    def __init__(self, list, pos):
        self.type = RSHIFT
        self.list = list
        self.pos = pos

    def __str__(self):
        return "(rshift(" + str(self.list) + ',' + str(self.pos) +  "))"

    def interpret(self, envt):
        temp = deque(self.list)
        temp.rotate(self.pos)
        ret = []
        for x in temp:
            ret.append(x.interpret(envt))
        return ret

class Increment(Node):
    def __init__(self, list, num):
        self.type = INCREMENT
        self.list = list
        self.num = num

    def __str__(self):
        return "(increment(" + str(self.list) + ',' + str(self.num) +  "))"

    def interpret(self, envt):
        ret = []
        for x in self.list:
            ret.append(x.interpret(envt) + self.num) 
        return ret

class MultiplyList(Node):
    def __init__(self, list, num):
        self.type = MULTIPLYLIST
        self.list = list
        self.num = num

    def __str__(self):
        return "(multiplylist(" + str(self.list) + ',' + str(self.num) +  "))"

    def interpret(self, envt):
        ret = []
        for x in self.list:
            ret.append(x.interpret(envt) * self.num) 
        return ret

class IsEmpty(Node):
    def __init__(self, list):
        self.type = EMPTY
        self.list = list

    def __str__(self):
        return "(isEmpty(" + str(self.list)+ "))"

    def interpret(self, envt):
        return len(self.list) == 0

class Concat(Node):
    def __init__(self, list1, list2):
        self.type = CONCAT
        self.list1 = list1
        self.list2 = list2

    def __str__(self):
        return "(concat(" + str(self.list1) + ',' + str(self.list2) +  "))"

    def interpret(self, envt):
        return (self.list1.interpret(envt)) + (self.list2.interpret(envt))

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