import escherNestedIfElse as es
import structures as ops
from collections import deque
import time

def test_length():
    def length(l):
        return len(l[0])

    es.escher(
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

    es.escher(
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
    
def test_stutter():
    def stutter(l):
        new_list = []
        for element in l[0]:
            new_list.append(element)
            new_list.append(element)
        return new_list

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL, ops.EMPTYLIST, ops.CONS],
        [{"name": "x", "type": list}],
        [],
        [{"x": [], "_out": []}, 
        {"x": [5], "_out": [5,5]},
        {"x": [5,6,3], "_out": [5,5,6,6,3,3]}, 
        {"x": [6,5], "_out": [6,6,5,5]}, 
        {"x": [5,6], "_out": [5,5,6,6]}, 
        {"x": [6], "_out": [6,6]}, 
        {"x": [5,3], "_out": [5,5,3,3]}, 
        {"x": [5,5], "_out": [5,5,5,5]}, 
        {"x": [6,3], "_out": [6,6,3,3]}, 
        {"x": [3,3], "_out": [3,3,3,3]}, 
        {"x": [3], "_out": [3,3]}],
        stutter
    )

def test_square_list():
    def square_list(l):
        new_list = []
        for element in range(1, l[0]+1):
            new_list.append(element*element)
        return new_list

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.TIMES, ops.NEG, ops.DECNUM],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.ISPOSITIVE, ops.LT],
        [ops.ISEMPTY, ops.ISPOSITIVE],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.EMPTYLIST, ops.CONS, ops.CONCAT],
        [{"name": "x", "type": int}],
        [0],
        [{"x": 0, "_out": []}, 
        {"x": 1, "_out": [1]},
        {"x": 2, "_out": [1,4]}, 
        {"x": -3, "_out": []}, 
        {"x": 3, "_out": [1,4,9]}, 
        {"x": 4, "_out": [1,4,9,16]}],
        square_list
    )

def test_insert():
    def insert_list(l):
        new_list = l[0].copy()

        if(l[1] <= 0):
            new_list.insert(0, l[2])
        else:
            new_list.insert(l[1], l[2])
        return new_list

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD, ops.DECNUM, ops.NEG],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.ISPOSITIVE, ops.LT],
        [ops.ISEMPTY, ops.ISPOSITIVE, ops.OR],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL, ops.CONS],
        [{"name": "x", "type": list}, {"name": "y", "type": int}, {"name": "z", "type": int}],
        [],
        [{"x": [], "y":0, "z":5, "_out": [5]},
        {"x": [3], "y":-1, "z":1, "_out": [1,3]},
        {"x": [1,2,3], "y":0, "z":8, "_out": [8, 1, 2, 3]},
        {"x": [1,2,3], "y":1, "z":8, "_out": [1, 8, 2, 3]},
        {"x": [1,2,3], "y":2, "z":8, "_out": [1, 2, 8, 3]},
        {"x": [1,2,3], "y":3, "z":8, "_out": [1, 2, 3, 8]}
        ],
        insert_list
    )

def test_fib():
    def fib(l):
        if(l[0] > 10000):
            return "ERROR"
        if(l[0] <= 0 or l[0] == 1):
            return l[0]

        prevprev = 0
        prev = 0
        curr = 1
        for i in range(1, l[0]):
            prevprev = prev
            prev = curr
            curr = prevprev + prev

        return curr

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.PLUS, ops.DECNUM],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.ISPOSITIVE, ops.LT],
        [ops.EQUAL, ops.OR],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [],
        [{"name": "x", "type": int}],
        [0, 1],
        [{"x": 0, "_out": 0},
        {"x": 1, "_out": 1},
        {"x": 2, "_out": 1},
        {"x": 3, "_out": 2},
        {"x": 4, "_out": 3},
        {"x": 9, "_out": 34},
        {"x": 10, "_out": 55},
        {"x": 11, "_out": 89},
        ],
        fib
    )

def test_sum_under():
    def sum_under(l):
        if(l[0] > 10000):
            return "ERROR"
        sum = 0
        for i in range(0, l[0]+1):
            sum += i
        return sum

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.NEG, ops.ZERO, ops.PLUS, ops.DECNUM],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.ISPOSITIVE, ops.LT],
        [ops.ISPOSITIVE],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [],
        [{"name": "x", "type": int}],
        [],
        [
        {"x": -5, "_out": 0},
        {"x": -1, "_out": 0},    
        {"x": 0, "_out": 0},
        {"x": 1, "_out": 1},
        {"x": 2, "_out": 3},
        {"x": 3, "_out": 6},
        {"x": 4, "_out": 10},
        {"x": 5, "_out": 15},
        {"x": 6, "_out": 21},
        ],
        sum_under
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

    es.escher(
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

def test_contains():
    def contains(l):
        return l[1] in l[0]

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY, ops.EQUAL, ops.FALSE_exp, ops.TRUE_exp],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL],
        [{"name": "x", "type": list}, {"name": "y", "type": int}],
        [],
        [{"x": [],"y": 1, "_out": False}, 
        {"x": [1,2],"y": 3, "_out": False}, 
        {"x": [1,2,3],"y": 1, "_out": True}, 
        {"x": [1,2,3],"y": -1, "_out": False}, 
        {"x": [1,2,3],"y": 2, "_out": True},
        {"x": [1,2,3],"y": 3, "_out": True},  
        {"x": [1,2,3],"y": 4, "_out": False}, 
        ],
        contains
    )

def test_last_in_list():
    def last_in_list(l):
        if(len(l[0]) <= 0):
            return "ERROR"
        else:
            return l[0][-1]

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL],
        [{"name": "x", "type": list}],
        [],
        [{"x": [], "_out": "ERROR"}, 
        {"x": [1], "_out": 1},
        {"x": [1,2,3], "_out": 3},  
        {"x": [1,6,7,11], "_out": 11},
        {"x": [10,25,7,9,18], "_out": 18},  
        ],
        last_in_list
    )

def test_drop_last():
    def drop_last(l):
        if(len(l[0]) <= 0):
            return []
        else:
            return l[0][0:len(l[0])-1]

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL, ops.EMPTYLIST, ops.CONS],
        [{"name": "x", "type": list}],
        [],
        [{"x": [], "_out": []}, 
        {"x": [1], "_out": []},
        {"x": [1,2], "_out": [1]},
        {"x": [1,2,3], "_out": [1,2]},
        {"x": [1,1,1,2,3,2], "_out": [1,1,1,2,3]},
        ],
        drop_last
    )

def test_evens():
    def evens_in_list(l):
        new_arr = []
        i = 0
        while(i < len(l[0])):
            new_arr.append(l[0][i])
            i+=2
        return new_arr

    es.escher(
        #[ops.PLUS, ops.MINUS, ops.TIMES, ops.INCNUM, ops.DECNUM, ops.NEG, ops.DIV2, ops.HEAD, ops.ZERO],
        [ops.HEAD],
        #[ops.FALSE_exp, ops.AND, ops.OR, ops.NOT, ops.EQUAL, ops.ISEMPTY, ops.ISNEGATIVE, ops.LT],
        [ops.ISEMPTY],
        #[ops.TAIL, ops.CONS, ops.CONCAT, ops.INCLIST, ops.DECLIST, ops.EMPTYLIST, ops.ZEROLIST],
        [ops.TAIL, ops.EMPTYLIST, ops.CONS],
        [{"name": "x", "type": list}],
        [],
        [{"x": [], "_out": []}, 
        {"x": [1], "_out": [1]},
        {"x": [1,2], "_out": [1]},
        {"x": [1,2,3,4], "_out": [1,3]},
        {"x": [1,2,3,4,5,6], "_out": [1,3,5]},
        ],
        evens_in_list
    )

if __name__ == "__main__":
    tic = time.perf_counter()
    # Standard Case Works (DO NOT RUN ALL AT ONCE AS IT CAN GET VERY MEMORY INTENSIVE)
    #test_length()
    #test_reverse()
    #test_square_list()
    #test_stutter()
    #test_fib()
    #test_insert()

    # Nested cases (Working)
    #test_compress()
    #test_last_in_list()
    #test_drop_last()
    #test_evens()
    
    # Standard Case Doesn't work ?
    #test_sum_under()
    
    # Nested cases (Not working?)
    #test_contains()

    toc = time.perf_counter()
    print("Time: " + str(toc-tic))
    
