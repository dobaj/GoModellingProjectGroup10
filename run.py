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
    CASE_NUMBER = int(sys.argv[2])

GRID_SIZE = 5


class Hashable:
    """Used to compare propositions to each other."""
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)
    
# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding

# 
"""Coords are (i,j). Boards 1 and 3 are from problem formulation."""


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



class Test:
    def __init__(self, description: str, board: dict, captured: bool) -> None:
        self.description = description
        self.board = board
        self.captured = captured # our answer 

        self.blk_dots = set()
        self.wht_dots = set()
        self.oob_dots = set()
        self.srr_dots = set()

    

    def run(self, show_board: bool=False):

        def is_stone(i, j) -> bool:
            if BlackOccupied(f"i{i}",f"j{j}") in self.blk_dots:
                return True
            if WhiteOccupied(f"i{i}",f"j{j}") in self.wht_dots:
                return True
            return False

        def surrounded(i, j) -> bool:
            if BlackOccupied(f"i{i}",f"j{j}") in self.blk_dots:
                return False
            if is_stone(i+1,j) and is_stone(i,j+1) and is_stone(i-1,j) and is_stone(i,j-1):
                return True
            return False

        def out_of_bounds(i, j) -> bool:
            if (i < 0 or j < 0 or i >= GRID_SIZE or j >= GRID_SIZE):
                return True
            return False

        def print_dots():
            for j in range(GRID_SIZE):
                out = ""
                for i in range(GRID_SIZE):
                    if BlackOccupied(f"i{i}",f"j{j}") in self.blk_dots:
                        out+="⚫"
                    elif Surrounded(f"i{i}", f"j{j}") in self.srr_dots:
                        out+="🚫"
                    elif WhiteOccupied(f"i{i}",f"j{j}") in self.wht_dots:
                        out+="⚪"
                    else:
                        out+="🟫"
                print(out)


        def add_propositions_from_board(board: dict):

            black_stones = board["black"]
            white_stones = board["white"]
            for i in range(-1,GRID_SIZE+1):
                for j in range(-1,GRID_SIZE+1):
                    if out_of_bounds(i,j):
                        self.E.add_constraint(OutOfBounds(f"i{i}",f"j{j}"))
                        self.oob_dots.add(OutOfBounds(f"i{i}",f"j{j}"))
                        continue
                    
                    if (i,j) in black_stones:
                        self.E.add_constraint(BlackOccupied(f"i{i}",f"j{j}"))
                        self.blk_dots.add(BlackOccupied(f"i{i}",f"j{j}"))
                    else:
                        self.E.add_constraint(~BlackOccupied(f"i{i}",f"j{j}"))


                    if (i,j) in white_stones:
                        self.E.add_constraint(WhiteOccupied(f"i{i}",f"j{j}"))
                        self.wht_dots.add(WhiteOccupied(f"i{i}",f"j{j}"))
                    else:
                        self.E.add_constraint(~WhiteOccupied(f"i{i}",f"j{j}"))    

        def add_constraints():
            # adds all constraints to global E
            for dot in self.blk_dots:
                i,j = dot.i,dot.j
                #Cannot have both dots on same pos
                self.E.add_constraint(~(BlackOccupied(i,j) & WhiteOccupied(i,j))) 
            for dot in self.oob_dots:
                i,j = dot.i, dot.j
                self.E.add_constraint(OutOfBounds(i,j)>>BlackOccupied(i,j))
                self.blk_dots.add(BlackOccupied(i,j)) #All oob_dots are considered black dots
            for i in range(GRID_SIZE):
                for j in range(GRID_SIZE):
                    #If there is a white dot in this pos
                    if WhiteOccupied(f"i{i}",f"j{j}") in self.wht_dots:
                        if surrounded(i,j):
                            self.E.add_constraint(Surrounded(f"i{i}",f"j{j}"))
                            self.srr_dots.add(Surrounded(f"i{i}",f"j{j}"))
                        else:
                            self.E.add_constraint(~Surrounded(f"i{i}",f"j{j}"))
                            self.E.add_constraint(~WhiteCaptured())
                    else:
                        self.E.add_constraint(~Surrounded(f"i{i}",f"j{j}"))
            self.E.add_constraint(WhiteCaptured())


        self.E = Encoding()


        @proposition(self.E)
        class WhiteOccupied(Hashable):

            def __init__(self, i, j):
                self.i = i
                self.j = j

            def __repr__(self):
                return f"({self.i} {self.j} W)"
            
        @proposition(self.E)
        class BlackOccupied(Hashable):

            def __init__(self, i, j):
                self.i = i
                self.j = j

            def __repr__(self):
                return f"({self.i} {self.j} B)"

        @proposition(self.E)
        class OutOfBounds(Hashable):

            def __init__(self, i, j):
                self.i = i
                self.j = j

            def __repr__(self):
                return f"({self.i} {self.j} O)"

        @proposition(self.E)
        class Surrounded(Hashable):

            def __init__(self, i, j):
                self.i = i
                self.j = j

            def __repr__(self):
                return f"({self.i} {self.j} S)"
            
        @proposition(self.E)
        class WhiteCaptured(Hashable):

            def __init__(self):
                self

            def __repr__(self):
                return f"White Captured?"
        
        add_propositions_from_board(self.board)
        add_constraints()

        if show_board:
            print("\n"+"-"*50)
            print_dots()

        # print(E)
        T = self.E.compile()
        # print(E.debug_constraints)
        # print(T)

        supposed_capturable = T.satisfiable()
        solutions = count_solutions(T)


        if supposed_capturable == self.captured:
            # we solved this test case
            print(f"✅ [{self.description}] cptable: {supposed_capturable}")
        else:
            print(f"❌ [{self.description}] answer: {self.captured} cptable: {supposed_capturable}")

   

        return T
        

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
	Test(
		'complicated case, no liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (2,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		},
		True,
	),   
	Test(
		'complicated case, 2 liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		},
		False,
	), 
	Test(
		'full board white',
		{
			"white": {(i,j) for i in range(5) for j in range(5)},
			"black": {},
		},
		True,
	), 

    Test(
		'full board white, two eyes',
		{
			"white": {(i,j) for i in range(5) for j in range(5) if (i,j) not in [(1,2),(4,0)]},
			"black": {},
		},
		False,
	), 
    

]



# tests = [
#         Test(
#             'single white stone surrounded by black',
#             {
#                 "white": {(1,2)},
#                 "black": {(1,3),(0,2),(2,2),(1,1)},
#             },
#             True,
#         ),
        
# ]

# def show_tests():
    


def run_tests():
    """
    Run a list of board configurations and what they should evaluate to. Prints to console.
    """

    
    for test in tests:
        test.run(show_board=True)

    # for test in reversed(tests):
    #     test.run()



    # for test in tests:
    #     T = test.run()


    # tests.reverse()
    
    # for test in tests:
    #     T = test.run()


if __name__ == "__main__":

    if MODE == 'run':

        if CASE_NUMBER in range(len(tests)):
            tests[CASE_NUMBER].run(show_board=True)
        
       

    elif MODE == 'test':
        print("\n"*2)
        run_tests()
        print("\n"*2)

    

