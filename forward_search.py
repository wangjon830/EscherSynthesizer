import structures as ops
import itertools

def initplist(vars, consts, intOps, boolOps, listOps):
    newInts, newLists, newBools = [], [], []
    for var in vars:
        if(var["type"] == int):
            newInts.append(ops.IntVar(var["name"]))
        elif(var["type"] == list):
            newLists.append(ops.ListVar(var["name"]))
            
    newInts += map(ops.Num, consts)

    if ops.FALSE_exp in boolOps:
        newBools.append(ops.FalseExp())

    if ops.TRUE_exp in boolOps:
        newBools.append(ops.TrueExp())

    if ops.ZERO in intOps:
        newInts.append(ops.Zero())

    if ops.EMPTYLIST in listOps:
        newLists.append(ops.EmptyList())

    return [newInts, newLists, newBools]

def heuristic(prog):
    vals = []
    for key in prog.__dict__:
        val = 1
        if(isinstance(prog.__dict__[key], ops.Node)):
            val += heuristic(prog.__dict__[key])
        elif(isinstance(prog.__dict__[key], list)):
            for p in prog.__dict__[key]:
                if(isinstance(p, ops.Node)):
                    val += heuristic(p)
        vals.append(val)
    return max(vals)

def grow(plist, intOps, boolOps, listOps, oracleInfo, heurlevel):
    newInts, newLists, newBools = [], [], []

    selfInputs = None
    for i in range(0, len(oracleInfo["inputs"])):
        if(oracleInfo["inputs"][i]["type"] == int):
            if(selfInputs == None):
                selfInputs = plist[0]
            else:
                selfInputs = list(map(lambda x: list(x), list(itertools.product(selfInputs, plist[0]))))
        elif(oracleInfo["inputs"][i]["type"] == list):
            if(selfInputs == None):
                selfInputs = plist[1]
            else:
                selfInputs = list(map(lambda x: list(x), list(itertools.product(selfInputs, plist[1]))))
        elif(oracleInfo["inputs"][i]["type"] == bool):
            if(selfInputs == None):
                selfInputs = plist[2]
            else:
                selfInputs = list(map(lambda x: list(x), list(itertools.product(selfInputs, plist[2]))))
        for j in range(0, len(selfInputs)):
            arg = []
            if(isinstance(selfInputs[j], list)):
                for el in selfInputs[j]:
                    if(isinstance(el, list)):
                        arg += el
                    else:
                        arg.append(el)
                selfInputs[j] = arg
    if(selfInputs != None):
        for args in selfInputs:
            if(len(oracleInfo["inputs"]) == 1):
                args = [args]
            new_prog = ops.Self(oracleInfo, args)
            if(heuristic(new_prog) <= heurlevel):
                if(oracleInfo["output"] == int):
                    newInts.append(new_prog)
                elif(oracleInfo["output"] == list):
                    newLists.append(new_prog)
                elif(oracleInfo["output"] == bool):
                    newBools.append(new_prog)

    
    for intProg1 in plist[0]:
        if ops.ISNEGATIVE in boolOps:
            new_prog = ops.IsNegative(intProg1)
            if(heuristic(new_prog) <= heurlevel):
                newBools.append(new_prog)
        if ops.INCNUM in intOps:
            new_prog = ops.IncrementNum(intProg1)
            if(heuristic(new_prog) <= heurlevel):
                newInts.append(new_prog)
        if ops.DECNUM in intOps:
            new_prog = ops.DecrementNum(intProg1)
            if(heuristic(new_prog) <= heurlevel):
                newInts.append(new_prog)
        if ops.NEG in intOps:
            new_prog = ops.Neg(intProg1)
            if(heuristic(new_prog) <= heurlevel):
                newInts.append(new_prog)
        if ops.DIV2 in intOps:
            new_prog = ops.Div2(intProg1)
            if(heuristic(new_prog) <= heurlevel):
                newInts.append(new_prog)
        if ops.ZEROLIST in listOps:
            new_prog = ops.ZeroList(intProg1)
            if(heuristic(new_prog) <= heurlevel):
                newLists.append(new_prog)
        
        for intProg2 in plist[0]:
            if ops.PLUS in intOps:
                new_prog = ops.Plus(intProg1, intProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newInts.append(new_prog)
            if ops.MINUS in intOps:
                new_prog = ops.Minus(intProg1, intProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newInts.append(new_prog)
            if ops.TIMES in intOps and intProg1.type == ops.INTVAR:
                new_prog = ops.Times(intProg1, intProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newInts.append(new_prog)
            if ops.LT in boolOps:
                new_prog = ops.Lt(intProg1, intProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newBools.append(new_prog)
            if ops.EQUAL in boolOps:
                new_prog = ops.Equals(intProg1, intProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newBools.append(new_prog)
        
        for listProg1 in plist[1]:
            if ops.CONS in listOps:
                new_prog = ops.Cons(intProg1, listProg1)
                if(heuristic(new_prog) <= heurlevel):
                    newLists.append(new_prog)

    for listProg1 in plist[1]:
        if ops.ISEMPTY in boolOps:
            new_prog = ops.IsEmpty(listProg1)
            if(heuristic(new_prog) <= heurlevel):
                newBools.append(new_prog)
        if ops.INCLIST in listOps:
            new_prog = ops.IncrementList(listProg1)
            if(heuristic(new_prog) <= heurlevel):
                newLists.append(new_prog)
        if ops.DECLIST in listOps:
            new_prog = ops.DecrementList(listProg1)
            if(heuristic(new_prog) <= heurlevel):
                newLists.append(new_prog)
        if ops.HEAD in intOps:
            new_prog = ops.Head(listProg1)
            if(heuristic(new_prog) <= heurlevel):
                newInts.append(new_prog)
        if ops.TAIL in listOps:
            new_prog = ops.Tail(listProg1)
            if(heuristic(new_prog) <= heurlevel):
                newLists.append(new_prog)
        
        for listProg2 in plist[1]:
            if ops.CONCAT in listOps:
                new_prog = ops.Concat(listProg1, listProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newLists.append(new_prog)

    for boolProg1 in plist[2]:
        if ops.NOT in boolOps:
            new_prog = ops.Not(boolProg1)
            if(heuristic(new_prog) <= heurlevel):
                newBools.append(new_prog)
                      
    plist[0] += newInts
    plist[1] += newLists
    plist[2] += newBools
    return plist

def elimEquivalents(plist, inputs, oracleInfo):
    newplist = [[],[],[]]

    for i in range(0, len(plist)):
        resultHash = {}
        for p in plist[i]:
            result = ''
            for input in inputs:
                result += str(p.interpret(input)) + ','
            pHeur = heuristic(p)
            if((result not in resultHash or resultHash[result][1] > pHeur)):
                resultHash[result] = [p, pHeur]
        newplist[i] = [item[0] for item in resultHash.values()]

    return newplist

def opListToString(opList):
    ret = "["
    for op in opList:
        ret += str(op)
        ret += ", "
    ret += "]"
    return ret

def test(intOps, boolOps, listOps, vars, consts, inputoutputs, oracleFun):
    oracleInputs = []
    for var in vars:
        oracleInputs.append(var)
    oracleOutput = type(inputoutputs[0]["_out"])
    oracleInfo = {"fun":oracleFun, "inputs":oracleInputs, "output":oracleOutput}

    plist = initplist(vars, consts, intOps, boolOps, listOps)
    print(opListToString(plist[0]+plist[1]+plist[2]))

    iters = 4
    baseHeur = 1
    for x in range(baseHeur+1, iters+baseHeur+1):
        plist = grow(plist, intOps, boolOps, listOps, oracleInfo, x)
        plist = elimEquivalents(plist, inputoutputs, oracleInfo)
        #print(opListToString(plist[0]+plist[1]+plist[2]))


    #print(opListToString(plist[0]+plist[1]+plist[2]))
    #print(len(plist[0]+plist[1]+plist[2]))
    for prog in plist[0]+plist[1]+plist[2]:
        res = ''
        [out, correct] = ops.getOutput(prog, inputoutputs)
        res += str(out) + ' ' + str(correct)
        #print(str(prog) + " " + res)
    #print(str(prog) + ' ' + str(heuristic(prog)))
    
    #testRec = ops.Plus(ops.Div2(ops.IntVar('a')), ops.Times(ops.IntVar('b'), ops.IntVar('c')))
    #print(ops.getRecursiveCall(testRec))

    #testP = ops.Div2(ops.Self(oracleInfo, [ops.Concat(ops.ListVar('b'), ops.ListVar('b')), ops.IntVar('a')]))
    #print(ops.getRecursiveCall(testP))
    #print(str(testP) + ': ' + str(ops.checkRecurse(testP, inputoutputs, oracleInfo)))
    correctLength = ops.Ite(ops.IsEmpty(ops.ListVar('x')), ops.Zero(), ops.IncrementNum(ops.Self(oracleInfo, [ops.Tail(ops.ListVar('x')), ops.IntVar('y')])))
    print(ops.testRecurse(correctLength, inputoutputs, oracleInfo))
    #print(str(correctLength) + ': ' + str(ops.checkRecurse(correctLength, inputoutputs, oracleInfo)))

    nonTerminatingLength = ops.Self(oracleInfo, [ops.ListVar('x'), ops.IntVar('y')])
    print(ops.testRecurse(nonTerminatingLength, inputoutputs, oracleInfo))
    #print(str(nonTerminatingLength) + ': ' +  str(ops.checkRecurse(nonTerminatingLength, inputoutputs, oracleInfo)))



if __name__ == "__main__":
    # Oracle functions can only take 1 input being a list of inputs
    def length(l):
        return len(l[0])
    test(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.INCNUM, ops.ZERO],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT, ops.ITE],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL],
        [{"name": "x", "type": list}, {"name": "y", "type": int}],
        [],
        [{"x":[5,1,2,3],"y":3, "_out":4},{"x":[1,1,2],"y":3, "_out":3}, {"x":[1],"y":3, "_out":1}, {"x":[],"y":3, "_out":0}],
        length
    )