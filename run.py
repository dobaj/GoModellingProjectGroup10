import sys

from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()

GRID_SIZE = 5
CASE_NUMBER = -1
SHOWBOARD = False
if len(sys.argv) > 1:
	arguments = sys.argv[1:]
	if arguments[0] == "--help":
		print("USAGE: run.py [optional test-case] [optional --showboard]")
		exit(1)
	if arguments[0].isdecimal():
		CASE_NUMBER = int(sys.argv[1])
		arguments = arguments[1:]
	if len(arguments) > 0:
		SHOWBOARD = arguments[0] == "--showboard"




class Hashable:
	"""Used to compare propositions to each other."""
	def __hash__(self):
		return hash(str(self))

	def __eq__(self, __value: object) -> bool:
		return hash(self) == hash(__value)

	def __repr__(self):
		return str(self)
	
# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding
# def print_board(sol):
#     """Unused. Using print dots instead in case there is no solution.
#     Keeping this in case we change to a multiple solution model.
#     """
#     for j in range(GRID_SIZE):
#         out = ""
#         for i in range(GRID_SIZE):
#             if sol[BlackOccupied(f"i{i}",f"j{j}")]:
#                 out+="⚫"
#             elif sol[Surrounded(f"i{i}", f"j{j}")]:
#                 out+="🚫"
#             elif sol[WhiteOccupied(f"i{i}",f"j{j}")]:
#                 out+="⚪"
#             else:
#                 out+="🟫"
#         print(out)

class Test:
	def __init__(self, description: str, board: dict, captured: bool) -> None:
		self.description = description
		self.board = board
		self.captured = captured # our answer 



	

	def run(self, show_board: bool=False) -> bool:
		self.E = Encoding()

		self.blk_stones = set()
		self.wht_stones = set()
		self.oob_stones = set()
		self.safe_stones = set()
		self.cap_stones = set()

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
		class Safe(Hashable):

			def __init__(self, i, j):
				self.i = i
				self.j = j

			def __repr__(self):
				return f"({self.i} {self.j} S)"
			
		@proposition(self.E)
		class Captured(Hashable):

			def __init__(self, i, j):
				self.i = i
				self.j = j

			def __repr__(self):
				return f"({self.i} {self.j} C)"
			
		def is_stone(i, j) -> bool:
			if BlackOccupied(f"i{i}",f"j{j}") in self.blk_stones:
				return True
			if WhiteOccupied(f"i{i}",f"j{j}") in self.wht_stones:
				return True
			return False

		def safe(i, j) -> bool:
			for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
				if WhiteOccupied(f"i{i+di}",f"j{j+dj}") in self.wht_stones and Safe(f"i{i+di}",f"j{j+dj}") not in self.safe_stones:
					self.E.add_constraint(Safe(f"i{i+di}",f"j{j+dj}"))
					self.safe_stones.add(Safe(f"i{i+di}",f"j{j+dj}"))
					safe(i+di,j+dj)

		def out_of_bounds(i, j) -> bool:
			if (i < 0 or j < 0 or i >= GRID_SIZE or j >= GRID_SIZE):
				return True
			return False

		def add_from_board(board: dict):
			black_stones = board["black"]
			white_stones = board["white"]
			for i in range(-1,GRID_SIZE+1):
				for j in range(-1,GRID_SIZE+1):
					if out_of_bounds(i,j):
						self.E.add_constraint(OutOfBounds(f"i{i}",f"j{j}"))
						self.oob_stones.add(OutOfBounds(f"i{i}",f"j{j}"))
						continue
					
					if (i,j) in black_stones:
						self.E.add_constraint(BlackOccupied(f"i{i}",f"j{j}"))
						self.blk_stones.add(BlackOccupied(f"i{i}",f"j{j}"))
					else:
						self.E.add_constraint(~BlackOccupied(f"i{i}",f"j{j}"))


					if (i,j) in white_stones:
						self.E.add_constraint(WhiteOccupied(f"i{i}",f"j{j}"))
						self.wht_stones.add(WhiteOccupied(f"i{i}",f"j{j}"))
					else:
						self.E.add_constraint(~WhiteOccupied(f"i{i}",f"j{j}"))    

		def add_constraints():
			# return
			# adds all constraints to global E
			for dot in self.blk_stones:
				i,j = dot.i,dot.j
				#Cannot have both dots on same pos
				self.E.add_constraint(~(BlackOccupied(f"i{i}",f"j{j}") & WhiteOccupied(f"i{i}",f"j{j}"))) 
			for dot in self.oob_stones:
				i,j = dot.i, dot.j
				self.E.add_constraint(OutOfBounds(i,j)>>BlackOccupied(i,j))
				self.blk_stones.add(BlackOccupied(i,j)) #All oob_dots are considered black dots
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					#If there is a white dot in this pos
					if WhiteOccupied(f"i{i}",f"j{j}") not in self.wht_stones and BlackOccupied(f"i{i}",f"j{j}") not in self.blk_stones:
						safe(i,j)
					# else:
					# 	self.E.add_constraint(~Safe(f"i{i}",f"j{j}"))
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					if WhiteOccupied(f"i{i}",f"j{j}")  in self.wht_stones and Safe(f"i{i}",f"j{j}"):
						self.E.add_constraint(Captured(f"i{i}",f"j{j}"))
						self.cap_stones.add(Captured(f"i{i}",f"j{j}"))
			# self.E.add_constraint(WhiteCaptured())
		
		def print_dots():
			for j in range(GRID_SIZE):
				out = ""
				for i in range(GRID_SIZE):
					if BlackOccupied(f"i{i}",f"j{j}") in self.blk_stones:
						out+="⚫"
					elif Captured(f"i{i}", f"j{j}") in self.cap_stones:
						out+="🚫"
					elif WhiteOccupied(f"i{i}",f"j{j}") in self.wht_stones:
						out+="⚪"
					else:
						out+="🟫"
				print(out)

		add_from_board(self.board)
		add_constraints()

		if show_board:
			print("\n"+"-"*50)
			print_dots()

		T = self.E.compile()

		satisfiable = T.satisfiable()
		# solutions = count_solutions(T)


		if satisfiable == True:
			whites = 0
			for w in self.wht_stones:
				whites+=1
			caps=0
			for cap in self.cap_stones:
				caps+=1
			# we solved this test case
			if caps == whites:
				print(f"✅ Capturable: {str(satisfiable):<5}\t\t\t[{self.description}] ")
			else:
				print(f"❌ Capturable: {str(satisfiable):<5}\tAnswer: {self.captured}\t[{self.description}]  ")
			print(f"Amount Captured: {caps}")

		return satisfiable
	
	
	def next_move(self) -> bool:
		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				if (i,j) in self.board["black"]:
					continue

				if (i,j) in self.board["white"]:
					continue

				# we can safely test and add a black to the square
				self.board["black"].add((i,j))

				print(f"testing at {i,j}")
				satisfiable = self.run(show_board=True)

				self.board["black"].remove((i,j))

				
				if satisfiable:
					return True
				
		return False
		
		
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
	
	Test(
		'overlapping stones, not capturable',
		{
			"white": {(2,2)},
			"black": {(2,2)},
		},
		False,
	),
	Test(
		'overlapping stones',
		{
			"white": {(1,2)},
			"black": {(1,3),(0,2),(2,2),(1,1),(1,2)},
		},
		False,
	),
	Test(
		'overlapping stones, complicated case, no liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (2,0), (1,1), (3,1), (1,2), (1,3), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		},
		False,
	),   

]


	



def run_tests():
	"""
	Run a list of board configurations and what they should evaluate to. Prints to console.
	"""
	for test in tests:
		test.run(show_board=SHOWBOARD)





if __name__ == "__main__":
	# if CASE_NUMBER in range(len(tests)):
	#         print()
	#         tests[CASE_NUMBER].run(show_board=SHOWBOARD)
	#         print()
	# else: #test
	#     print()
	#     run_tests()
	#     print()
	run_tests()
	print()
	
	t = Test(
		'complicated case, 2 liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		},
		False,
	)
	
	# t = Test(
	# 	'single white stone surrounded by 3 black',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(2,2),(1,1)},
	# 	},
	# 	False,
	# )

	