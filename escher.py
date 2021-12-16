import structures as ops
import forward_search as fs

class GoalGraph():
    def __init__(self):
        self.root = []
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

memo = []
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

def splitgoal(syn, goalGraph):
    for program in syn:
        for goal in goalGraph.G:
            progGoal = []

            index = 0
            while index < len(memo[program]):
                if goal[index] == "?" or memo[program][index] == goal[index]:
                    progGoal[index] = True
                else:
                    progGoal[index] = False

            if progGoal not in branches:
                newResolver = Resolver()
                newResolver.ifgoal = progGoal
                thenVector = []
                elseVector = []

                index = 0
                while index < len(progGoal):
                    if progGoal[index]:
                        thenVector[index] = goalGraph.root[index]
                        elseVector[index] = "?"
                    else:
                        thenVector[index] = "?"
                        elseVector[index] = goalGraph.root[index]

                newResolver.thengoal = thenVector
                newResolver.thenSat = program
                newResolver.elsegoal = elseVector

                goalGraph.R.add(newResolver)

                goalGraph.G.add(progGoal)
                goalGraph.G.add(thenVector)
                goalGraph.G.add(elseVector)

                goalGraph.E.add((progGoal, newResolver))
                goalGraph.E.add((thenVector, newResolver))
                goalGraph.E.add((elseVector, newResolver))
                goalGraph.E.add((newResolver, goal))


def match(program, goal):
    index = 0
    while index < len(program):
        if goal[index] == "?":
            index += 1
            continue
        if goal[index] != program[index]:
            return False
        index += 1
    return True

def resolve(syn, goalGraph):
    for r in goalGraph.R:
        for program in syn:
            if match(memo[program], r.ifgoal):
                r.ifSat = program
            if match(memo[program], r.thengoal):
                r.thenSat = program
            if match(memo[program], r.elsegoal):
                r.elseSat = program
        if r.ifSat is not None and r.thenSat is not None and r.elseSat is not None:
            return r
    return None

def saturate():
    return

def escher(syn, goalGraph, intOps, boolOps, listOps, vars, consts, inputoutputs, oracleFun):
    oracleInputs = []
    for var in vars:
        oracleInputs.append(var["type"])
    oracleOutput = type(inputoutputs[0]["_out"])
    oracleInfo = {"fun": oracleFun, "inputs": oracleInputs, "output": oracleOutput}

    plist = fs.initplist(vars, consts, intOps, boolOps, listOps)

    plist = fs.grow(plist, intOps, boolOps, listOps, oracleInfo)
    plist = fs.elimEquivalents(plist, inputoutputs)
    splitgoal(plist, goalGraph)
    resolve(syn, goalGraph)
    for r in goalGraph.R:
        print(r.ifgoal)
        print(r.thengoal)
        print(r.elsegoal)
        print(r.ifSat)
        print(r.thenSat)
        print(r.elseSat)


if __name__ == "__main__":
    def length(l):
        return len(l[0])
    gr = GoalGraph()
    gr.root = [4, 4]

    escher(
        [],
        gr,
        [ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD],
        # [ops.DECNUM],
        [ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        # [],
        [ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        # [],
        [{"name": "x", "type": list}, {"name": "y", "type": int}],
        [],
        [{"x": [5, 1, 2, 3], "y": 3, "_out": 4}, {"x": [1, 1, 2, 3], "y": 2, "_out": 4}],
        length
    )

