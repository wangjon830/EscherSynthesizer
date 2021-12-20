import structures as ops
import forward_search as fs

class GoalGraph():
    def __init__(self, root):
        self.root = root
        self.G = [self.root]
        self.R = []
        self.E = []
        self.Ites = []


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
    syn = syn + goalGraph.Ites
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
    goalGraph.Ites.append(newNode)
    for edge in goalGraph.E:
        if edge[0] == r:
            if edge[1] == goalGraph.root:
                return newNode
            for e in goalGraph.E:
                if e[0] == edge[1]:
                    resolver = e[1]
                    if resolver.elseSat is None and resolver.elsegoal == e[0]:
                        resolver.elseSat = newNode
                        if resolver.ifSat is not None and resolver.thenSat is not None and resolver.elseSat is not None:
                            result = resolving(resolver, goalGraph)
                            if result:
                                return result
                    return None

def splitgoalMmm(syn, goalGraph, inputoutputs):
    goals = goalGraph.G.copy()
    for program in syn:
        for inde, goal in enumerate(goals):
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
            trueList = []
            for index, input in enumerate(inputoutputs):
                if goal[index] == '?':
                    progGoal[index] = '?'
                elif program.interpret(input) == goal[index]:
                    progGoal[index] = True
                    trueList.append(index)
                    matched += 1
                else:
                    progGoal[index] = False
                    notmatched += 1

            if matched == 0 or notmatched == 0:
                continue
            progs = pow(2, len(trueList))
            i = 0

            for index, val in enumerate(trueList):
                progGoal[val] = False

            while i < progs - 1:
                for index,val in enumerate(trueList):
                    if progGoal[val]:
                        progGoal[val] = False
                        continue
                    progGoal[val] = True
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
                        progGoal = progGoal.copy()
                    i +=1

def escher(intOps, boolOps, listOps, vars, consts, inputoutputs, oracleFun):
    goalGraph = GoalGraph([input['_out'] for input in inputoutputs])

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
        plist = fs.grow(plist, intOps, boolOps, listOps, oracleInfo, inputoutputs, level)
        plist = fs.elimEquivalents(plist, inputoutputs, oracleInfo)

        splitgoalMmm(plist[0]+plist[1]+plist[2], goalGraph, inputoutputs)
        ans = resolve(plist[0]+plist[1]+plist[2], goalGraph, inputoutputs)
        level += 1
        if level == 5:
            for r in goalGraph.R:
                new_str = ''
                new_str += str(r.ifgoal) + ' '
                new_str += str(r.ifSat) + ' '
                new_str += str(r.thengoal) + ' '
                new_str += str(r.thenSat) + ' '

                new_str += str(r.elsegoal) + ' '
                new_str += str(r.elseSat) + ' '

                print(new_str)

    if(ops.testRecurse(ans, inputoutputs, oracleInfo)):
        print('Found Prog: ' + str(ans) + '\nInputs ' + str(inputoutputs) + '\nLevel: ' + str(level))
        return ans
    else:
        print('Found ERROR Prog: ' + str(ans) + '\nInputs ' + str(inputoutputs) + '\nLevel: ' + str(level))

def test_length():
    def length(l):
        return len(l[0])

    escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.INCNUM, ops.ZERO],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL],
        [{"name": "x", "type": list}],
        [],
        [{"x": [5, 1, 2, 3], "_out": 4}, {"x": [2,3], "_out": 2}, {"x": [1], "_out": 1}, {"x": [], "_out": 0}],
        length
    )

def test_reverse():
    def reverse(l):
        new_list = []
        for i in reversed(l[0]):
            new_list.append(i)
        return new_list

    escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL, ops.EMPTYLIST, ops.CONS, ops.CONCAT],
        [{"name": "x", "type": list}],
        [],
        [{"x": [5, 1, 2, 3], "_out": [3,2,1,5]}, {"x": [2,3], "_out": [3,2]}, {"x": [1], "_out": [1]}, {"x": [], "_out": []}],
        reverse
    )

def test_compress():
    def compress(l):
        new_list = []
        i = 0
        curr_el = None
        while(i < len(l[0])):
            if(curr_el != None):
                while(i < len(l[0]) and l[0][i] == curr_el):
                    i += 1
                if(i < len(l[0])):
                    curr_el = l[0][i]
                    new_list.append(curr_el)
            else:
                curr_el = l[0][i]
                new_list.append(curr_el)
            i += 1
        return new_list

    escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY, ops.EQUAL],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL, ops.EMPTYLIST, ops.CONS],
        [{"name": "x", "type": list}],
        [],
        [{"x": [], "_out": []}, {"x": [7], "_out": [7]},
        {"x": [9,9], "_out": [9]},
        {"x": [3,9], "_out": [3,9]},
        {"x": [2,3,9], "_out": [2,3,9]},
        {"x": [9,9,2], "_out": [9,2]},
        {"x": [3,3,3,9], "_out": [3,9]},
        {"x": [2,3,3,9,9], "_out": [2,3,9]}],
        compress
    )

if __name__ == "__main__":
    #test_length()
    #test_reverse()
    test_compress()

