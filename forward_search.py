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
        if(prog.type == ops.SELF):
            val = 0
        else:
            val = 1
        if(isinstance(prog.__dict__[key], ops.Node)):
            val += heuristic(prog.__dict__[key])
        elif(isinstance(prog.__dict__[key], list)):
            sub_vals = []
            for p in prog.__dict__[key]:
                sub_val = 0
                if(isinstance(p, ops.Node)):
                    sub_val += heuristic(p)
                sub_vals.append(sub_val)
            if(len(sub_vals) > 0):
                val += max(sub_vals)
        vals.append(val)
    return max(vals)

def grow(plist, intOps, boolOps, listOps, oracleInfo, inputoutputs, heurlevel):
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
            if(heuristic(new_prog) <= heurlevel and ops.isTerminating(new_prog, inputoutputs, oracleInfo)):
                if(oracleInfo["output"] == int):
                    newInts.append(new_prog)
                elif(oracleInfo["output"] == list):
                    newLists.append(new_prog)
                elif(oracleInfo["output"] == bool):
                    newBools.append(new_prog)

    
    for intProg1 in plist[0]:
        if(intProg1.type != ops.NUM):
            if ops.ISNEGATIVE in boolOps:
                new_prog = ops.IsNegative(intProg1)
                if(heuristic(new_prog) <= heurlevel):
                    newBools.append(new_prog)
            if ops.ISPOSITIVE in boolOps:
                new_prog = ops.IsPositive(intProg1)
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
            if ops.EQUAL in boolOps:
                new_prog = ops.Equals(listProg1, listProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newBools.append(new_prog)

    for boolProg1 in plist[2]:
        if ops.NOT in boolOps:
            new_prog = ops.Not(boolProg1)
            if(heuristic(new_prog) <= heurlevel):
                newBools.append(new_prog)

        for boolProg2 in plist[2]:
            if ops.AND in boolOps:
                new_prog = ops.And(boolProg1, boolProg2)
                if(heuristic(new_prog) <= heurlevel):
                    newBools.append(new_prog)
            if ops.OR in boolOps:
                new_prog = ops.Or(boolProg1, boolProg2)
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