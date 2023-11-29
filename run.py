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
#             if sol[BlackOccupied(i, j)]:
#                 out+="⚫"
#             elif sol[Surrounded(f"i{i}", f"j{j}")]:
#                 out+="🚫"
#             elif sol[WhiteOccupied(i, j)]:
#                 out+="⚪"
#             else:
#                 out+="🟫"
#         print(out)

class Test:
	def __init__(self, description: str, board: dict, captured: bool) -> None:
		self.description = description
		self.board = board
		self.answer = captured # our answer 



	

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
				return f"(i{self.i} j{self.j} W)"
			
		@proposition(self.E)
		class BlackOccupied(Hashable):

			def __init__(self, i, j):
				self.i = i
				self.j = j

			def __repr__(self):
				return f"(i{self.i} j{self.j} B)"

		@proposition(self.E)
		class Safe(Hashable):

			def __init__(self, i, j):
				self.i = i
				self.j = j

			def __repr__(self):
				return f"(i{self.i} j{self.j} S)"
			
		@proposition(self.E)
		class Captured(Hashable):

			def __init__(self, i, j):
				self.i = i
				self.j = j

			def __repr__(self):
				return f"(i{self.i} j{self.j} C)"
			
		def is_stone(i, j) -> bool:
			if BlackOccupied(i,j) in self.blk_stones:
				return True
			if WhiteOccupied(i,j) in self.wht_stones:
				return True
			return False

		def safe(i, j) -> bool:
			for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
				if WhiteOccupied(i+di,j+dj) in self.wht_stones and Safe(i+di,j+dj) not in self.safe_stones:
					self.E.add_constraint(Safe(i+di,j+dj))
					self.safe_stones.add(Safe(i+di,j+dj))
					safe(i+di,j+dj)

		def add_from_board(board: dict):
			black_stones = board["black"]
			white_stones = board["white"]
			for i in range(-1,GRID_SIZE+1):
				for j in range(-1,GRID_SIZE+1):
					if (i,j) in black_stones:
						self.E.add_constraint(BlackOccupied(i, j))
						self.blk_stones.add(BlackOccupied(i, j))
					else:
						self.E.add_constraint(~BlackOccupied(i, j))

					if (i,j) in white_stones:
						self.E.add_constraint(WhiteOccupied(i, j))
						self.wht_stones.add(WhiteOccupied(i, j))
					else:
						self.E.add_constraint(~WhiteOccupied(i, j))    

		def add_constraints():
			# return
			# adds all constraints to global E
			for dot in self.blk_stones:
				i,j = dot.i,dot.j
				#Cannot have both dots on same pos, cant have a safe dot be captured
				self.E.add_constraint(~(BlackOccupied(i, j) & WhiteOccupied(i, j)) )
				self.E.add_constraint(~(Safe(i, j) & Captured(i, j))) 
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					#If there is a liberty here
					if not is_stone(i,j):
						safe(i,j)
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					#If a white stone is not safe then it is captured
					if WhiteOccupied(i, j) in self.wht_stones and Safe(i, j) not in self.safe_stones:
						self.E.add_constraint(Captured(i, j))
						self.cap_stones.add(Captured(i, j))
		
		def print_answer():
			for j in range(GRID_SIZE):
				out = ""
				for i in range(GRID_SIZE):
					if BlackOccupied(i, j) in self.blk_stones:
						out+="⚫"
					elif Captured(i, j) in self.cap_stones:
						out+="🚫"
					elif WhiteOccupied(i, j) in self.wht_stones:
						out+="⚪"
					else:
						out+="🟫"
				print(out)

		add_from_board(self.board)
		add_constraints()

		if show_board:
			print("\n"+"-"*50)
			print_answer()

		T = self.E.compile()

		satisfiable = T.satisfiable()
		# solutions = count_solutions(T)

		# if satisfiable == True:
		# whites = len(self.wht_stones)
		# caps = len(self.cap_stones)
		# answer = (caps == whites) & satisfiable
		# # we solved this test case
		# if answer == self.answer:
		# 	print(f"✅ Capturable: {str(answer):<5}\t\t\t[{self.description}] ")
		# else:
		# 	print(f"❌ Capturable: {str(answer):<5}\tAnswer: {self.answer}\t[{self.description}]  ")
		# print(f"Amount Captured: {caps}")

		return satisfiable

	def print_dots(self):
			for j in range(GRID_SIZE):
				out = ""
				for i in range(GRID_SIZE):
					if (i, j) in self.board["black"]:
						out+="⚫"
					elif (i, j) in self.board["white"]:
						out+="⚪"
					else:
						out+="🟫"
				print(out)

	def swap_boards(self):
		temp = set(self.board["black"])
		self.board["black"] = self.board["white"]
		self.board["white"] = temp
	
	def next_black_move(self) -> bool:
		self.print_dots()
		max_score = -1
		black_stone_pos = (-1,-1)
		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				satisfiable = True
				if (i,j) in self.board["black"]:
					continue

				if (i,j) in self.board["white"]:
					continue
				
				#Remove already captured stones from both sides
				self.run()
				for cap in self.cap_stones:
					self.board["white"].remove((cap.i,cap.j))
				self.swap_boards()
				self.run()
				for cap in self.cap_stones:
					self.board["white"].remove((cap.i,cap.j))
				self.swap_boards()
				# we can  add a black stone to the square
				black = set(self.board["black"])
				white = set(self.board["white"])

				self.board["black"].add((i,j))
				#See if the move is illegal
				self.swap_boards()
				self.run()
				for cap in self.cap_stones:
					if (cap.i,cap.j) == (i,j):
						satisfiable = False
				self.swap_boards()
				# print(f"testing black stone at {i,j}")
				print("#",end="",flush=True)

				satisfiable &= self.run(show_board=False)
				if satisfiable:
					score = len(self.cap_stones)
					score -= self.next_white_move()
					#Reset board positions for next iteration
					self.board["black"] = black
					self.board["white"] = white
					#If best move so far then set max
					# print(score, (i,j))
					max_score = max(max_score,score)
					if max_score == score:
						black_stone_pos = (i,j)
		print()
		return max_score, black_stone_pos

	def next_white_move(self) -> bool:
		max_score = 0
		self.swap_boards()
		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				satisfiable = True
				if (i,j) in self.board["black"]:
					continue

				if (i,j) in self.board["white"]:
					continue
				
				#Remove already captured stones
				self.run()
				for cap in self.cap_stones:
					self.board["white"].remove((cap.i,cap.j))
				self.swap_boards()
				self.run()
				for cap in self.cap_stones:
					self.board["white"].remove((cap.i,cap.j))
				self.swap_boards()

				# we can safely test and add a black to the square
				self.board["black"].add((i,j))
				#See if the move is illegal
				self.swap_boards()
				self.run()
				for cap in self.cap_stones:
					if (cap.i,cap.j) == (i,j):
						satisfiable = False
				self.swap_boards()

				# print(f"testing at {i,j}")
				satisfiable &= self.run(show_board=False)
				if satisfiable:
					max_score = max(len(self.cap_stones), max_score)
					self.board["black"].remove((i,j))
		return max_score

		
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
		# test.run(show_board=SHOWBOARD)
		print(test.next_black_move())





if __name__ == "__main__":
	# if CASE_NUMBER in range(len(tests)):
	#         print()
	#         tests[CASE_NUMBER].run(show_board=SHOWBOARD)
	#         print()
	# else: #test
	#     print()
	#     run_tests()
	#     print()
	# run_tests()
	
	print()
	
	t = Test(
		'single white stone surrounded by 3 black one white',
		{
			"white": {(1,2)},
			"black": {(1,3),(2,2),(1,1)},
		},
		False,
	)
	output= t.next_black_move()
	print("Best move is:",output[1]," with score:", output[0])

	# t = Test(
	# 	'single white stone surrounded by 3 black',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(2,2),(1,1)},
	# 	},
	# 	False,
	# )
	# t.next_move()

	