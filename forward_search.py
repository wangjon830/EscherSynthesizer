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
    val = 1
    for key in prog.__dict__:
        if(isinstance(prog.__dict__[key], ops.Node)):
            val += heuristic(prog.__dict__[key])
        elif(isinstance(prog.__dict__[key], list)):
            for p in prog.__dict__[key]:
                if(isinstance(p, ops.Node)):
                    val += heuristic(p)
    return val

def grow(plist, intOps, boolOps, listOps, oracleInfo):
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
                print('test')
                for el in selfInputs[j]:
                    if(isinstance(el, list)):
                        arg += el
                    else:
                        arg.append(el)
                selfInputs[j] = arg
    for args in selfInputs:
        if(len(oracleInfo["inputs"]) == 1):
            args = [args]
        if(oracleInfo["output"] == int):
            newInts.append(ops.Self(oracleInfo, args))
        elif(oracleInfo["output"] == list):
            newLists.append(ops.Self(oracleInfo, args))
        elif(oracleInfo["output"] == bool):
            newBools.append(ops.Self(oracleInfo, args))

    
    for intProg1 in plist[0]:
        if ops.ISNEGATIVE in boolOps:
            newBools.append(ops.IsNegative(intProg1))
        if ops.INCNUM in intOps:
            newInts.append(ops.IncrementNum(intProg1))
        if ops.DECNUM in intOps:
            newInts.append(ops.DecrementNum(intProg1))
        if ops.NEG in intOps:
            newInts.append(ops.Neg(intProg1))
        if ops.DIV2 in intOps:
            newInts.append(ops.Div2(intProg1))
        if ops.ZEROLIST in listOps:
            newLists.append(ops.ZeroList(intProg1))
        
        for intProg2 in plist[0]:
            if ops.PLUS in intOps:
                newInts.append(ops.Plus(intProg1, intProg2))
            if ops.MINUS in intOps:
                newInts.append(ops.Minus(intProg1, intProg2))
            if ops.TIMES in intOps and intProg1.type == ops.INTVAR:
                newInts.append(ops.Times(intProg1, intProg2))
            if ops.LT in boolOps:
                newBools.append(ops.Lt(intProg1, intProg2))
            if ops.EQUAL in boolOps:
                newBools.append(ops.Equals(intProg1, intProg2))
        
        for listProg1 in plist[1]:
            if ops.CONS in listOps:
                newLists.append(ops.Cons(intProg1, listProg1))

    for listProg1 in plist[1]:
        if ops.ISEMPTY in boolOps:
            newBools.append(ops.IsEmpty(listProg1))
        if ops.INCLIST in listOps:
            newLists.append(ops.IncrementList(listProg1))
        if ops.DECLIST in listOps:
            newLists.append(ops.DecrementList(listProg1))
        if ops.HEAD in intOps:
            newInts.append(ops.Head(listProg1))
        if ops.TAIL in listOps:
            newLists.append(ops.Tail(listProg1))
        
        for listProg2 in plist[1]:
            if ops.CONCAT in listOps:
                newLists.append(ops.Concat(listProg1, listProg2))

    for boolProg1 in plist[2]:
        if ops.NOT in boolOps:
            newBools.append(ops.Not(boolProg1))
                      
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
    #print(opListToString(plist[0]+plist[1]+plist[2]))
    
    iters = 3
    for x in range(0, iters):
        plist = grow(plist, intOps, boolOps, listOps, oracleInfo)
        plist = elimEquivalents(plist, inputoutputs, oracleInfo)
    print(opListToString(plist[0]+plist[1]+plist[2]))

    #print(opListToString(plist[0]+plist[1]+plist[2]))
    #print(len(plist[0]+plist[1]+plist[2]))
    for prog in plist[0]+plist[1]+plist[2]:
        res = ''
        [out, correct] = ops.getOutput(prog, inputoutputs)
        res += str(out) + ' ' + str(correct)
        print(str(prog) + " " + res)
    #print(str(prog) + ' ' + str(heuristic(prog)))
    
    #testP = ops.Div2(ops.Self(oracleInfo, [ops.Concat(ops.ListVar('b'), ops.ListVar('b')), ops.IntVar('a')]))
    #print(str(testP) + ': ' + str(ops.checkRecurse(testP, inputoutputs, oracleInfo)))
    #correctLength = ops.Ite(ops.IsEmpty(ops.ListVar('b')), ops.Zero(), ops.IncrementNum(ops.Self(oracleInfo, [ops.Tail(ops.ListVar('b')), ops.IntVar('a')])))
    #print(str(correctLength) + ': ' + str(ops.checkRecurse(correctLength, inputoutputs, oracleInfo)))

    #nonTerminatingLength = ops.Self(oracleInfo, [ops.ListVar('b'), ops.IntVar('a')])
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
        [{"name":"b", "type": list}],
        [],
        [{"b":[5,1,2,3], "_out":4},{"b":[1,1,2], "_out":3}, {"b":[1], "_out":1}, {"b":[], "_out":0}],
        length
    )