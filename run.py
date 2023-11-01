import sys

from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()

if len(sys.argv) <= 1:
    print("USAGE: run.py [MODE: RUN | TEST] (BOARD VERSION)")
    exit(1)
MODE = sys.argv[1].lower()

if MODE == 'run':
    VERSION = int(sys.argv[2])

GRID_SIZE = 5
blk_dots = set()
wht_dots = set()
oob_dots = set()
srr_dots = set()
surrounded = []

class Hashable:
    """Used to compare propositions to each other."""
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)
    
# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding
@proposition(E)
class WhiteOccupied(Hashable):

    def __init__(self, i, j):
        self.i = i
        self.j = j

    def __repr__(self):
        return f"({self.i} {self.j} W)"
    
@proposition(E)
class BlackOccupied(Hashable):

    def __init__(self, i, j):
        self.i = i
        self.j = j

    def __repr__(self):
        return f"({self.i} {self.j} B)"

@proposition(E)
class OutOfBounds(Hashable):

    def __init__(self, i, j):
        self.i = i
        self.j = j

    def __repr__(self):
        return f"({self.i} {self.j} O)"

@proposition(E)
class Surrounded(Hashable):

    def __init__(self, i, j):
        self.i = i
        self.j = j

    def __repr__(self):
        return f"({self.i} {self.j} S)"
    
@proposition(E)
class WhiteCaptured(Hashable):

    def __init__(self):
        self

    def __repr__(self):
        return f"White Captured?"
# 
"""Coords are (i,j). Boards 1 and 3 are from problem formulation."""
black_squares = {
    1:{(0,0), (2,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
    2:{(0,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
    3:{(1,0),(0,1),(4,1),(3,2),(2,3),(4,3),(3,4)},

    4:{(1,0),(0,1),(2,1),(1,2)},
    5:{},
    6:{},
    7:{(2,2)},
    8:{(i,j) for i in range(5) for j in range(5)},
    9:{},
    10:{(1,2)},




    }
white_squares = {
    1:{(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
    2:{(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
    3:{(0,0), (4,0), (1,3), (3,3)},

    4:{(0,0),(1,1)},
    5: {(i,j) for i in range(5) for j in range(5)},
    6:{(i,j) for i in range(5) for j in range(5) if (i,j) != (2,2)},
    7:{(i,j) for i in range(5) for j in range(5) if (i,j) != (2,2)},
    8:{},
    9:{},
    10:{},


    }

# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def build_theory():
    global E
    example_game(VERSION)
    add_constraints()




def is_stone(i, j) -> bool:
    if BlackOccupied(f"i{i}",f"j{j}") in blk_dots:
        return True
    if WhiteOccupied(f"i{i}",f"j{j}") in wht_dots:
        return True
    return False

def surrounded(i, j) -> bool:
    if BlackOccupied(f"i{i}",f"j{j}") in blk_dots:
        return False
    if is_stone(i+1,j) and is_stone(i,j+1) and is_stone(i-1,j) and is_stone(i,j-1):
        return True
    return False

def out_of_bounds(i, j) -> bool:
    if (i < 0 or j < 0 or i >= GRID_SIZE or j >= GRID_SIZE):
        return True
    return False

def example_game(version):
    #Use range outside of grid to populate out of bounds propositions
    for i in range(-1,GRID_SIZE+1):
        for j in range(-1,GRID_SIZE+1):
            if out_of_bounds(i,j):
                E.add_constraint(OutOfBounds(f"i{i}",f"j{j}"))
                oob_dots.add(OutOfBounds(f"i{i}",f"j{j}"))
            else:
                if (i,j) in black_squares[version]:
                    E.add_constraint(BlackOccupied(f"i{i}",f"j{j}"))
                    blk_dots.add(BlackOccupied(f"i{i}",f"j{j}"))
                else:
                    E.add_constraint(~BlackOccupied(f"i{i}",f"j{j}"))
                if (i,j) in white_squares[version]:
                    E.add_constraint(WhiteOccupied(f"i{i}",f"j{j}"))
                    wht_dots.add(WhiteOccupied(f"i{i}",f"j{j}"))
                else:
                    E.add_constraint(~WhiteOccupied(f"i{i}",f"j{j}"))
            
def add_propositions_from_board(board: dict):
    global E

    black_stones = board["black"]
    white_stones = board["white"]
    for i in range(-1,GRID_SIZE+1):
        for j in range(-1,GRID_SIZE+1):
            if out_of_bounds(i,j):
                E.add_constraint(OutOfBounds(f"i{i}",f"j{j}"))
                oob_dots.add(OutOfBounds(f"i{i}",f"j{j}"))
                continue
            
            if (i,j) in black_stones:
                E.add_constraint(BlackOccupied(f"i{i}",f"j{j}"))
                blk_dots.add(BlackOccupied(f"i{i}",f"j{j}"))
            else:
                E.add_constraint(~BlackOccupied(f"i{i}",f"j{j}"))


            if (i,j) in white_stones:
                E.add_constraint(WhiteOccupied(f"i{i}",f"j{j}"))
                wht_dots.add(WhiteOccupied(f"i{i}",f"j{j}"))
            else:
                E.add_constraint(~WhiteOccupied(f"i{i}",f"j{j}"))    


def add_constraints():
    global E
    # adds all constraints to global E
    for dot in blk_dots:
        i,j = dot.i,dot.j
        #Cannot have both dots on same pos
        E.add_constraint(~(BlackOccupied(i,j) & WhiteOccupied(i,j))) 
    for dot in oob_dots:
        i,j = dot.i, dot.j
        E.add_constraint(OutOfBounds(i,j)>>BlackOccupied(i,j))
        blk_dots.add(BlackOccupied(i,j)) #All oob_dots are considered black dots
    for i in range(GRID_SIZE):
        for j in range(GRID_SIZE):
            #If there is a white dot in this pos
            if WhiteOccupied(f"i{i}",f"j{j}") in wht_dots:
                if surrounded(i,j):
                    E.add_constraint(Surrounded(f"i{i}",f"j{j}"))
                    srr_dots.add(Surrounded(f"i{i}",f"j{j}"))
                else:
                    E.add_constraint(~Surrounded(f"i{i}",f"j{j}"))
                    E.add_constraint(~WhiteCaptured())
            else:
                E.add_constraint(~Surrounded(f"i{i}",f"j{j}"))
    E.add_constraint(WhiteCaptured())

def print_board(sol):
    """Unused. Using print dots instead in case there is no solution.
    Keeping this in case we change to a multiple solution model.
    """
    for j in range(GRID_SIZE):
        out = ""
        for i in range(GRID_SIZE):
            if sol[BlackOccupied(f"i{i}",f"j{j}")]:
                out+="⚫"
            elif sol[Surrounded(f"i{i}", f"j{j}")]:
                out+="🚫"
            elif sol[WhiteOccupied(f"i{i}",f"j{j}")]:
                out+="⚪"
            else:
                out+="🟫"
        print(out)

def print_dots():
    for j in range(GRID_SIZE):
        out = ""
        for i in range(GRID_SIZE):
            if BlackOccupied(f"i{i}",f"j{j}") in blk_dots:
                out+="⚫"
            elif Surrounded(f"i{i}", f"j{j}") in srr_dots:
                out+="🚫"
            elif WhiteOccupied(f"i{i}",f"j{j}") in wht_dots:
                out+="⚪"
            else:
                out+="🟫"
        print(out)

class Test:
    def __init__(self, description: str, board: dict, captured: bool) -> None:
        self.description = description
        self.board = board
        self.captured = captured # our answer 

    def run(self):
        # global E
        # E.purge_propositions()
        E = Encoding()

        # print(E)
        
        add_propositions_from_board(self.board)
        add_constraints()
        # print(E)
        T = E.compile()
        # print(E.debug_constraints)
        # print(T)

        supposed_capturable = T.satisfiable()
        solutions = count_solutions(T)

        if supposed_capturable == self.captured:
            # we solved this test case
            print(f"✅ {self.description}")
        else:
            print(f"❌ {self.description} should: {self.captured} was: {supposed_capturable}")

        # E.clear_constraints()
        # E.clear_debug_constraints()

        return T
        






def run_tests():
    """
    Run a list of board configurations and what they should evaluate to. Prints to console.
    """

    tests = [
        Test(
            'empty board',
            {
                "white": {},
                "black": {},
            },
            True,
        ),
        Test(
            'single black stone',
            {
                "white": {},
                "black": {(1,2)},
            },
            True,
        ),
        Test(
            'single white stone',
            {
                "white": {(1,2)},
                "black": {},
            },
            False,
        ),
        Test(
            'single white stone surrounded by black',
            {
                "white": {(1,2)},
                "black": {(1,3),(0,2),(2,2),(1,1)},
            },
            True,
        ),
        Test(
            'single white stone surrounded by 3 black',
            {
                "white": {(1,2)},
                "black": {(1,3),(2,2),(1,1)},
            },
            False,
        ),      
        Test(
            'single white stone surrounded by 3 black one white',
            {
                "white": {(1,2),(0,2)},
                "black": {(1,3),(2,2),(1,1)},
            },
            False,
        ),     
    ]

    for test in tests:
        test.run()

    for test in reversed(tests):
        test.run()



    # for test in tests:
    #     T = test.run()


    # tests.reverse()
    
    # for test in tests:
    #     T = test.run()


if __name__ == "__main__":

    if MODE == 'run':

        build_theory()
        print(E.debug_constraints)
        # Don't compile until you're finished adding all your constraints!
        T = E.compile()

        # After compilation (and only after), you can check some of the properties
        # of your model:
        print("\nSatisfiable: %s" % T.satisfiable())
        print("# Solutions: %d" % count_solutions(T))
        # print("   Solution: %s" % T.solve())
        sol = T.solve()
        # print("\nVariable likelihoods:")
        # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
        #     # Ensure that you only send these functions NNF formulas
        #     # Literals are compiled to NNF here
        #     print(" %s: %.2f" % (vn, likelihood(T, v)))
        # print()

        if sol == None:
            print("White is not captured")
            print_dots()
        else:
            print("White is captured.")
            print_dots()

    elif MODE == 'test':
        print("\n"*2)
        run_tests()
        print("\n"*2)

    

