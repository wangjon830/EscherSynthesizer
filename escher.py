import structures as ops
import forward_search as fs

class GoalGraph():
    def __init__(self, root):
        self.root = root
        self.G = [self.root]
        self.R = []
        self.E = []


class Resolver():
    def __init__(self):
        self.ifgoal = []
        self.ifSat = None

        self.thengoal = []
        self.thenSat = None

        self.elsegoal = []
        self.elseSat = None

memo = {}
branches = []
def testProgram(syn, inputoutputs):
    for program in syn:
        count = 0
        for i, inputoutput in enumerate(inputoutputs):
            out = program.interpret(inputoutput)
            print (
                f'{i + 1}. Evaluating programs {program}\non inputoutput examples {inputoutput}. The output of the program is {out}\n')
            if out == inputoutput["_out"]:
                count += 1
            else:
                break
        if len(inputoutputs) == count:
            return program
    return None

def elimEquvalent(plist, inputoutputs):
    newList = []
    for term in plist:
        exists = False
        for term2 in newList:
            count = 0
            for input in inputoutputs:
                if term.interpret(input) == term2.interpret(input):
                    count+=1
                else:
                    break
            if count == len(inputoutputs):
                exists = True
                break
        if not exists:
            newList.append(term)
    return newList

def splitgoal(syn, goalGraph, inputoutputs):
    goals = goalGraph.G.copy()
    for program in syn:
        for goal in goals:
            progGoal = [None]*len(inputoutputs)
            matched = 0
            notmatched = 0
            for index, input in enumerate(inputoutputs):
                if goal[index] == '?':
                    progGoal[index] = True
                elif program.interpret(input) == goal[index]:
                    progGoal[index] = True
                    matched = 1
                else:
                    progGoal[index] = False
                    notmatched = 1

            if matched == 0 or notmatched == 0:
                continue
            if progGoal not in goalGraph.G:
                newResolver = Resolver()
                newResolver.ifgoal = progGoal
                thenVector = [None]*len(inputoutputs)
                elseVector = [None]*len(inputoutputs)

                index = 0
                while index < len(progGoal):
                    if progGoal[index]:
                        thenVector[index] = goal[index]
                        elseVector[index] = "?"
                    else:
                        thenVector[index] = "?"
                        elseVector[index] = goal[index]
                    index += 1
                newResolver.thengoal = thenVector
                newResolver.thenSat = program
                newResolver.elsegoal = elseVector

                goalGraph.R.append(newResolver)

                goalGraph.G.append(progGoal)
                goalGraph.G.append(thenVector)
                goalGraph.G.append(elseVector)

                goalGraph.E.append((progGoal, newResolver))
                goalGraph.E.append((thenVector, newResolver))
                goalGraph.E.append((elseVector, newResolver))
                goalGraph.E.append((newResolver, goal))


def match(program, goal, inputoutputs):
    for index, input in enumerate(inputoutputs):
        if(goal[index] == '?'):
            continue
        if(goal[index] != program.interpret(input)):
            return False
    return True

def resolve(syn, goalGraph, inputoutputs):
    for r in goalGraph.R:
        for program in syn:
            if r.ifSat is None and match(program, r.ifgoal, inputoutputs):
                r.ifSat = program
            if r.elseSat is None and match(program, r.elsegoal, inputoutputs):
                r.elseSat = program
        if r.ifSat is not None and r.thenSat is not None and r.elseSat is not None:
            result = resolving(r, goalGraph)
            if result:
                return result

    return None

def resolving(r, goalGraph):
    newNode = ops.Ite(r.ifSat, r.thenSat, r.elseSat)
    for edge in goalGraph.E:
        if edge[0] == r:
            if edge[1] == goalGraph.root:
                return newNode
            for e in goalGraph.E:
                if e[0] == edge[1]:
                    resolver = e[1]
                    if resolver.ifSat is None and resolver.ifgoal == e[0]:
                        resolver.ifSat = program
                    if resolver.elseSat is None and resolver.elsegoal == e[0]:
                        resolver.elseSat = program
                    if resolver.ifSat is not None and resolver.thenSat is not None and resolver.elseSat is not None:
                        result = resolving(resolver, goalGraph)
                        if result:
                            return result
                    return None

def saturate():
    return

def escher(syn, goalGraph, intOps, boolOps, listOps, vars, consts, inputoutputs, oracleFun):
    oracleInputs = []
    for var in vars:
        oracleInputs.append(var)
    oracleOutput = type(inputoutputs[0]["_out"])
    oracleInfo = {"fun": oracleFun, "inputs": oracleInputs, "output": oracleOutput}

    plist = fs.initplist(vars, consts, intOps, boolOps, listOps)

    ans = None
    level = 1
    while(ans is None):
        print(level)
        plist = fs.grow(plist, intOps, boolOps, listOps, oracleInfo, level)
        plist = fs.elimEquivalents(plist, inputoutputs, oracleInfo)
        for prog in plist[0]+plist[1]+plist[2]:
            if("tail" in str(prog)):
                print(prog)
        splitgoal(plist[0]+plist[1]+plist[2], goalGraph, inputoutputs)
        ans = resolve(plist[0]+plist[1]+plist[2], goalGraph, inputoutputs)
        level += 1
        for r in goalGraph.R:
            new_str = ''
            new_str += str(r.ifgoal) + ' '
            new_str += str(r.ifSat) + ' '
            new_str += str(r.thengoal) + ' '
            new_str += str(r.thenSat) + ' '

            new_str += str(r.elsegoal) + ' '
            new_str += str(r.elseSat) + ' '

            print(new_str)

    print(ans)


if __name__ == "__main__":
    def length(l):
        return len(l[0])
    gr = GoalGraph([4,2,1,0])
    escher(
        [],
        gr,
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD],
        [ops.INCNUM, ops.ZERO],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL],
        [{"name": "x", "type": list}, {"name": "y", "type": int}],
        [],
        [{"x": [5, 1, 2, 3], "y": 3, "_out": 4}, {"x": [2,3], "y": 2, "_out": 2}, {"x": [1], "y": 2, "_out": 1}, {"x": [], "y": 2, "_out": 0}],
        length
    )

