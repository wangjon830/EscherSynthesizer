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

def splitgoal(syn, goalGraph, inputoutputs):
    goals = goalGraph.G.copy()
    for program in syn:
        for goal in goals:
            non = False
            for i in goal:
                if isinstance(i, bool):
                    non = True
                    break
            if(non):
                continue
            
            progGoal = [None]*len(inputoutputs)
            matched = 0
            notmatched = 0
            for index, input in enumerate(inputoutputs):
                if goal[index] == '?':
                    progGoal[index] = '?'
                elif program.interpret(input) == goal[index]:
                    progGoal[index] = True
                    matched += 1
                else:
                    progGoal[index] = False
                    notmatched += 1

            if matched == 0 or notmatched == 0:
                continue
            exists = 0
            for edge in goalGraph.E:
                if edge[1] == goal:
                    if goalMatch(edge[0].ifgoal, progGoal):
                        exists = 1

            if exists == 0:
                newResolver = Resolver()
                newResolver.ifgoal = progGoal
                thenVector = [None]*len(inputoutputs)
                elseVector = [None]*len(inputoutputs)

                index = 0
                while index < len(progGoal):
                    if progGoal[index] == "?":
                        thenVector[index] = "?"
                        elseVector[index] = "?"
                    elif progGoal[index]:
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

def goalMatch(goal1, goal2):
    for index, val in enumerate(goal1):
        if goal1[index] != goal2[index]:
            return False
    return True

def resolving(r, goalGraph):
    newNode = ops.Ite(r.ifSat, r.thenSat, r.elseSat)
    for edge in goalGraph.E:
        if edge[0] == r:
            if edge[1] == goalGraph.root:
                return newNode
            for e in goalGraph.E:
                if e[0] == edge[1]:
                    resolver = e[1]
                    if resolver.ifSat is None and goalMatch(resolver.ifgoal, e[0]):
                        resolver.ifSat = newNode
                    if resolver.elseSat is None and goalMatch(resolver.elsegoal, e[0]):
                        resolver.elseSat = newNode
                    if resolver.ifSat is not None and resolver.thenSat is not None and resolver.elseSat is not None:
                        result = resolving(resolver, goalGraph)
                        if result:
                            return result
                    return None

def escher(intOps, boolOps, listOps, vars, consts, inputoutputs, oracleFun):
    goalGraph = GoalGraph([input['_out'] for input in inputoutputs])

    oracleInputs = []
    for var in vars:
        oracleInputs.append(var)
    
    oracleOutput = type(inputoutputs[0]["_out"])
    for input in inputoutputs:
        if(input["_out"] != "ERROR"):
            oracleOutput = type(input["_out"])
    
    oracleInfo = {"fun": oracleFun, "inputs": oracleInputs, "output": oracleOutput}

    plist = fs.initplist(vars, consts, intOps, boolOps, listOps)
    ans = None
    level = 1
    while(ans is None):
        print('Synthesis level: ' + str(level))
        plist = fs.grow(plist, intOps, boolOps, listOps, oracleInfo, inputoutputs, level)
        plist = fs.elimEquivalents(plist, inputoutputs, oracleInfo)

        splitgoal(plist[0]+plist[1]+plist[2], goalGraph, inputoutputs)
        ans = resolve(plist[0]+plist[1]+plist[2], goalGraph, inputoutputs)
        level += 1

    if(ops.testRecurse(ans, inputoutputs, oracleInfo)):
        print('Found Prog: ' + str(ans) + '\nInputs ' + str(inputoutputs) + '\nLevel: ' + str(level))
        print(ops.getOutput(ans, inputoutputs))
        return ans
    else:
        print('Found ERROR Prog: ' + str(ans) + '\nInputs ' + str(inputoutputs) + '\nLevel: ' + str(level))
