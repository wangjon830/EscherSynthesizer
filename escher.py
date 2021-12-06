import structures.py

class GoalGraph():
    def __init__(self):
        self.G = {self.root}
        self.R = {}
        self.E = {}
        self.root = []

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

def forward(syn, ops):
    newSyn = []
    for op in ops:
        if op == PLUS or op == TIMES:
            for p in syn:
                typep = p.type
                if typep == ITE or typep == TIMES or typep == PLUS:
                    for term in syn:
                        type2 = term.type
                        if type2 == ITE or type2 == TIMES or type2 == PLUS or type2 == LENGTH or type2 == HEAD or type2 == TAIL or type2 == MAX or type2 == MIN:
                            if op == PLUS:
                                newSyn.append(Plus(p, term))
                            else:
                                newSyn.append(Times(p, term))

        elif op == ITE:
            for p in syn:
                typep = p.type
                if typep == AND or typep == NOT or typep == LT:
                    for term in syn:
                        type2 = term.type
                        if type2 == ITE or type2 == TIMES or type2 == PLUS or type2 == LENGTH or type2 == HEAD or type2 == TAIL or type2 == MAX or type2 == MIN:
                            for term2 in syn:
                                type3 = term2.type
                                if type3 == ITE or type3 == TIMES or type3 == PLUS or type3 == LENGTH or type3 == HEAD or type3 == TAIL or type3 == MAX or type3 == MIN:
                                    newSyn.append(Ite(p, term, term2))
        
        elif op == AND:
            for p in syn:
                typep = p.type
                if typep == AND or typep == NOT or typep == LT or typep == FALSE_exp:
                    for term in syn:
                        type2 = term.type
                        if type2 == AND or type2 == NOT or type2 == LT or type2 == FALSE_exp:
                            newSyn.append(And(p, term))

        elif op == NOT:
            for p in syn:
                typep = p.type
                if typep == AND or typep == NOT or typep == LT or typep == FALSE_exp:
                    newSyn.append(Not(p))

        elif op == LT:
            for p in syn:
                typep = p.type
                if typep == ITE or typep == TIMES or typep == PLUS or typep == VAR or typep == NUM:
                    for term in syn:
                        type2 = term.type
                        if type2 == ITE or type2 == TIMES or type2 == PLUS or type2 == LENGTH or type2 == HEAD or type2 == TAIL or type2 == MAX or type2 == MIN:
                            newSyn.append(Lt(p, term) )
        
        elif bool == LENGTH:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Length(p))

        elif bool == REVERSE:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Reverse(p))
         
         elif bool == SORT:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Sort(p))
        
        elif bool == LSHIFT:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Lshift(p))

        elif bool == RSHIFT:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Rshift(p))

        elif bool == INCREMENT:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Increment(p))
                    
        elif bool == MULTIPLYLIST:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(MultiplyList(p))

        elif bool == MAX:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Max(p))
                    
        elif bool == MIN:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Min(p))
                    

        elif bool == HEAD:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Head(p))


        elif bool == TAIL:
            for p in syn:
                typep = p.type
                if typep == LIST or typep == SORT or typep == LSHIFT or typep == RSHIFT or typep == INCREMENT or typep == MULTIPLYLIST:
                    newSyn.append(Tail(p))
    """
        check op and synthesize programs together
    """
    return newSyn


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

def splitgoal():
    return

def resolve():
    return

def saturate():
    return

def escher(syn, goalGraph, ops, inputoutputs, iterations):
    for inputoutput in inputoutputs:  # Init
        syn.append(inputoutput[0])
        goalGraph.root.append(inputoutput[1])

    iter = 1

    while iter < iterations:
        syn = forward(syn, ops)
        prog = testProgram(syn, inputoutputs)
        if prog is not None:
            return prog