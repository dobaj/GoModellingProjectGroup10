import sys

from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood
from os import get_terminal_size

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
		self.safe_stones = set()
		self.cap_white_stones = set()
		self.cap_black_stones = set()

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

		def safe(i, j, color) -> bool:
			for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
				if color == "any" or color == "white":
					if WhiteOccupied(i+di,j+dj) in self.wht_stones and Safe(i+di,j+dj) not in self.safe_stones:
						self.E.add_constraint(Safe(i+di,j+dj))
						self.safe_stones.add(Safe(i+di,j+dj))
						safe(i+di,j+dj,"white")
				if color == "any" or color == "black":
					if BlackOccupied(i+di,j+dj) in self.blk_stones and Safe(i+di,j+dj) not in self.safe_stones:
						self.E.add_constraint(Safe(i+di,j+dj))
						self.safe_stones.add(Safe(i+di,j+dj))
						safe(i+di,j+dj,"black")

		def add_from_board(board: dict):
			black_stones = board["black"]
			white_stones = board["white"]
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
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
						safe(i,j,"any")
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					#If a stone is not safe then it is captured
					if Safe(i, j) not in self.safe_stones:
						self.E.add_constraint(Captured(i, j))
						if WhiteOccupied(i, j) in self.wht_stones:
							self.cap_white_stones.add(Captured(i, j))
						elif BlackOccupied(i,j) in self.blk_stones:
							self.cap_black_stones.add(Captured(i, j))

		
		def print_answer():
			for j in range(GRID_SIZE):
				out = ""
				for i in range(GRID_SIZE):
					if Captured(i, j) in self.cap_black_stones:
						out+="🌑"
					elif BlackOccupied(i, j) in self.blk_stones:
						out+="⚫"
					elif Captured(i, j) in self.cap_white_stones:
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

	def print_line(self, clear = False):
		width = get_terminal_size().columns
		if clear:
			print("\r"+"─"*width+"\n")
		else:
			print("━"*width)

	def print_dots(self, display_moves = []):
		# Needs to have the board populated
		for j in range(GRID_SIZE):
			out = ""
			for i in range(GRID_SIZE):
				if (i,j) in display_moves:
					out+="🔴"
				elif  f"(i{i} j{j} C)" in self.cap_black_stones:
					out+="🌑"
				elif (i,j) in self.board["black"]:
					out+="⚫"
				elif f"(i{i} j{j} C)" in self.cap_white_stones:
					out+="🚫"
				elif (i,j) in self.board["white"]:
					out+="⚪"
				else:
					out+="🟫"
			print(out)

	def should_check(self, i, j, score):
		if (i,j) in self.board["black"] or (i,j) in self.board["white"]:
			return False
		
		# return True
	
		#Tentative
		for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
			if (i+di,j+dj) in self.board["black"] or (i+di,j+dj) in self.board["white"]:
				return True
		if score == None or score == 0:
			#Consider every 0 case
			return True
		return False

	def is_valid_move(self, i, j, player_set, other_set):
		#Sees if move at i j by player is valid.
		if f"(i{i} j{j} C)" in player_set:
			for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
				if f"(i{i+di} j{j+dj} C)" in other_set:
					#If this move captures enemy's piece then it is okay
					return True
			return False
		else:
			return True

	def remove_captured_stones(self, first):
		if first == "black" or first == "any":
			for cap in self.cap_black_stones:
				self.board["black"].remove((cap.i,cap.j))
			if first == "black":
				self.run()
			for cap in self.cap_white_stones:
				self.board["white"].remove((cap.i,cap.j))
		else:
			for cap in self.cap_white_stones:
				self.board["white"].remove((cap.i,cap.j))
			self.run()
			for cap in self.cap_black_stones:
				self.board["black"].remove((cap.i,cap.j))
	
	def next_black_move(self) -> bool:
		max_score = None
		black_stone_pos = [(-1,-1)]
		progress = 0
		total_runtime = GRID_SIZE**2
		#Remove already captured stones from both sides
		self.run()
		self.print_dots()
		
		self.remove_captured_stones("any")

		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				terminal_width = get_terminal_size().columns - 3
				progress_width = progress*terminal_width//total_runtime
				print("\r"+"["+"─"*progress_width+" "*(terminal_width-progress_width)+"]",end="",flush=True)
				progress+=1
				if not self.should_check(i,j,max_score):
					continue
				# we can add a black stone to the square
				black = set(self.board["black"])
				white = set(self.board["white"])

				self.board["black"].add((i,j))
				#Run test and see if the move is illegal
				satisfiable = self.run(show_board=False)
				satisfiable &= self.is_valid_move(i,j,self.cap_black_stones,self.cap_white_stones)
				if satisfiable:
					score = len(self.cap_white_stones)
					captured_white = set(self.cap_white_stones) # copy set
					#Remove already captured stones after this turn
					self.remove_captured_stones("white")
					white_move = self.next_white_move()
					score -= white_move[0]
					for b in range(len(white_move[2])):
						wi, wj = white_move[1][b]
						if f"(i{wi} j{wj} C)" in captured_white and white_move[0] > 1:
							self.cap_black_stones = white_move[2][b]
							self.cap_white_stones = set()
							self.board["white"].add((wi,wj))
							self.print_line(True)
							print("Potential snapback found - Black move:", (i,j), "White move:", white_move[1][b])
							self.print_dots()
					if max_score == None or score > max_score:
						max_score = score
						black_stone_pos = [(i,j)]
					elif score == max_score:
						black_stone_pos.append((i,j))
				
				#Reset board positions for next iteration
				self.board["black"] = black
				self.board["white"] = white
		self.print_line(True)
		self.run() #Refresh board positions
		return max_score, black_stone_pos

	def next_white_move(self) -> bool:
		max_score = None
		white_stone_pos = []
		black_cap = []
		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				if not self.should_check(i,j, max_score):
					continue
				
				# we can safely test and add a white stone to the square
				self.board["white"].add((i,j))
				#Run test and see if the move is illegal
				satisfiable = self.run(show_board=False)
				satisfiable &= self.is_valid_move(i,j,self.cap_white_stones,self.cap_black_stones)

				if satisfiable:
					score = len(self.cap_black_stones)
					if max_score == None or score > max_score:
						max_score = score
						white_stone_pos = [(i,j)]
						black_cap = [set(self.cap_black_stones)]
					elif score == max_score:
						white_stone_pos.append((i,j))
						black_cap.append(set(self.cap_black_stones))
				self.board["white"].remove((i,j))
		return max_score, white_stone_pos, black_cap
	
	def next_move(self):
		self.print_line()
		print("Test:", self.description, "\n")	
		output = self.next_black_move()
		if output[0] == None:
			print("No valid move can be played")
			return
		elif len(output[1]) > 1: 
			print("Best moves are:",output[1],"with score:", output[0], "(Note every best move is shown on the board)")
		else:
			print("Best move is:",output[1][0],"with score:", output[0])
		self.print_dots(output[1])
		
tests = [
	# Test(
	# 	'empty board',
	# 	{
	# 		"white": set(),
	# 		"black": set(),
	# 	},
	# 	True,
	# ),
	# Test(
	# 	'single black stone',
	# 	{
	# 		"white": set(),
	# 		"black": {(1,2)},
	# 	},
	# 	True,
	# ),
	# Test(
	# 	'single white stone',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": set(),
	# 	},
	# 	False,
	# ),
	# Test(
	# 	'single white stone surrounded by black',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(0,2),(2,2),(1,1)},
	# 	},
	# 	True,
	# ),
	# Test(
	# 	'single white stone surrounded by 3 black',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(2,2),(1,1)},
	# 	},
	# 	False,
	# ),      
	# Test(
	# 	'single white stone surrounded by 3 black one white',
	# 	{
	# 		"white": {(1,2),(0,2)},
	# 		"black": {(1,3),(2,2),(1,1)},
	# 	},
	# 	False,
	# ),  
	# Test(
	# 	'complicated case, no liberties',
	# 	{
	# 		"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
	# 		"black": {(0,0), (2,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
	# 	},
	# 	True,
	# ),   
	# Test(
	# 	'complicated case, 2 liberties',
	# 	{
	# 		"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
	# 		"black": {(0,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
	# 	},
	# 	False,
	# ), 
	# Test(
	# 	'full board white',
	# 	{
	# 		"white": {(i,j) for i in range(5) for j in range(5)},
	# 		"black": set(),
	# 	},
	# 	True,
	# ), 

	# Test(
	# 	'full board white, two eyes',
	# 	{
	# 		"white": {(i,j) for i in range(5) for j in range(5) if (i,j) not in [(1,2),(4,0)]},
	# 		"black": set(),
	# 	},
	# 	False,
	# ), 
	
	# Test(
	# 	'overlapping stones, not capturable',
	# 	{
	# 		"white": {(2,2)},
	# 		"black": {(2,2)},
	# 	},
	# 	False,
	# ),
	# Test(
	# 	'overlapping stones',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(0,2),(2,2),(1,1),(1,2)},
	# 	},
	# 	False,
	# ),
	# Test(
	# 	'overlapping stones, complicated case, no liberties',
	# 	{
	# 		"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
	# 		"black": {(0,0), (2,0), (1,1), (3,1), (1,2), (1,3), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
	# 	},
	# 	False,
	# ),  

    Test(
		'overlapping stones, complicated case, no liberties',
		{
			"white": {(1,0),(2,0),(3,0),(1,1),(1,2),(1,3),(1,4),(3,3),(4,1)},
			"black": {(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4),(4,2),(4,4)},
		},
		False,
	),   
	
    Test(
		'overlapping stones, complicated case, no liberties',
		{
			"white": {(1,0),(2,0),(3,1),(3,2),(3,3),(0,1),(1,2),(2,3)},
			"black": {(2,1),(1,1),(0,2),(0,3),(1,3)},
		},
		False,
	),   


]

def run_tests():
	"""
	Run a list of board configurations and what they should evaluate to. Prints to console.
	"""
	for test in tests:
		test.next_move()

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
	
	
	# t = Test(
	# 	'single white stone surrounded by 3 black one white',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(2,2),(1,1)},
	# 	},
	# 	False,
	# )
	# output = t.next_black_move()
	# print("Best move is:",output[1]," with score:", output[0])

	# t = Test(
	# 	'single white stone surrounded by 3 black',
	# 	{
	# 		"white": {(1,2)},
	# 		"black": {(1,3),(2,2),(1,1)},
	# 	},
	# 	False,
	# )
	# t.next_move()
