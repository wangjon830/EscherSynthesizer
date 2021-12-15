import structures as ops
import time
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
    for input in oracleInfo["inputs"]:
        if(input == int):
            if(selfInputs == None):
                selfInputs = plist[0]
            else:
                selfInputs = list(itertools.product(selfInputs, plist[0]))
        elif(input == list):
            if(selfInputs == None):
                selfInputs = plist[1]
            else:
                selfInputs = list(itertools.product(selfInputs, plist[1]))
        elif(input == bool):
            if(selfInputs == None):
                selfInputs = plist[2]
            else:
                selfInputs = list(itertools.product(selfInputs, plist[2]))
    for args in selfInputs:
        if(isinstance(args, tuple)):
            args = list(args)
        else:
            args = [args]
        if(oracleInfo["output"] == int):
            newInts.append(ops.Self(oracleInfo["fun"], args))
        elif(oracleInfo["output"] == list):
            newLists.append(ops.Self(oracleInfo["fun"], args))
        elif(oracleInfo["output"] == bool):
            newBools.append(ops.Self(oracleInfo["fun"], args))

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
        
        for boolProg2 in plist[2]:
            if ops.AND in boolOps:
                newBools.append(ops.And(boolProg1, boolProg2))
            if ops.OR in boolOps:
                newBools.append(ops.Or(boolProg1, boolProg2))

    plist[0] += newInts
    plist[1] += newLists
    plist[2] += newBools
    return plist

def elimEquivalents(plist, inputs):
    newplist = [[],[],[]]

    for i in range(0, len(plist)):
        resultHash = {}
        for p in plist[i]:
            result = ''
            for input in inputs:
                result += str(p.interpret(input)) + ','
            pHeur = heuristic(p)
            if(result not in resultHash or resultHash[result][1] > pHeur):
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
        oracleInputs.append(var["type"])
    oracleOutput = type(inputoutputs[0]["_out"])
    oracleInfo = {"fun":oracleFun, "inputs":oracleInputs, "output":oracleOutput}

    tic1 = time.perf_counter()
    plist = initplist(vars, consts, intOps, boolOps, listOps)
    print(opListToString(plist[0]+plist[1]+plist[2]))
    
    plist = grow(plist, intOps, boolOps, listOps, oracleInfo)
    #print(opListToString(plist[0]+plist[1]+plist[2]))
    plist = elimEquivalents(plist, inputoutputs)
    #print(opListToString(plist[0]+plist[1]+plist[2]))

    plist = grow(plist, intOps, boolOps, listOps, oracleInfo)
    plist = elimEquivalents(plist, inputoutputs)
    #print(opListToString(plist[0]+plist[1]+plist[2]))
    #plist = grow(plist, intOps, boolOps, listOps, oracleInfo)
    #plist = elimEquivalents(plist, inputoutputs)

    #print(opListToString(plist[0]+plist[1]+plist[2]))
    #print(len(plist[0]+plist[1]+plist[2]))
    for prog in plist[0]+plist[1]+plist[2]:
        if(ops.isCorrect(prog, inputoutputs)):
            print(str(prog))
            print(heuristic(prog))
        #print(str(prog) + ' ' + str(heuristic(prog)))



if __name__ == "__main__":
    # Oracle functions can only take 1 input being a list of inputs
    def length(l):
        return len(l[0])
    
    test(
        [ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD],
        #[ops.DECNUM],
        [ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        #[],
        [ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        #[],
        [{"name":"x", "type": list}, {"name":"y", "type": int}],
        [],
        [{"x":[5,1,2,3],"y":3, "_out":4},{"x":[1,1,2,3],"y":2, "_out":4}],
        length
    )