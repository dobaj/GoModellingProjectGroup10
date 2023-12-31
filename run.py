from bauhaus import Encoding, proposition
from os import get_terminal_size

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()

GRID_SIZE = 5



class Hashable:
	"""Used to compare propositions to each other."""
	def __hash__(self):
		return hash(str(self))

	def __eq__(self, __value: object) -> bool:
		return hash(self) == hash(__value)

	def __repr__(self):
		return str(self)

class Test:
	def __init__(self, description: str, board: dict) -> None:
		self.description = description
		self.board = board


	def run(self) -> bool:
		self.E = Encoding()

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
			
		# Sets to hold our propositions
		self.blk_stones = set()
		self.wht_stones = set()
		self.safe_stones = set()
		self.cap_white_stones = set()
		self.cap_black_stones = set()
			
		def is_stone(i, j) -> bool:
			"""Sees if a given location (i,j) has a stone."""
			if BlackOccupied(i,j) in self.blk_stones:
				return True
			if WhiteOccupied(i,j) in self.wht_stones:
				return True
			return False

		def safe(i, j, color) -> bool:
			"""Checks if a given color is safe based on whether it is adjacent to 
			either a stone of the same colour that is safe or a liberty."""
			for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
				if color == "any" or color == "white":
					if WhiteOccupied(i+di,j+dj) in self.wht_stones \
						and Safe(i+di,j+dj) not in self.safe_stones:
						self.E.add_constraint(Safe(i+di,j+dj))
						self.safe_stones.add(Safe(i+di,j+dj))
						safe(i+di,j+dj,"white")
				if color == "any" or color == "black":
					if BlackOccupied(i+di,j+dj) in self.blk_stones \
						and Safe(i+di,j+dj) not in self.safe_stones:
						self.E.add_constraint(Safe(i+di,j+dj))
						self.safe_stones.add(Safe(i+di,j+dj))
						safe(i+di,j+dj,"black")

		def add_from_board(board: dict):
			"""Fills constraints based on locations defined in our board dictionary."""
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
			"""Adds extra constraints such as no overlapping 
			black/white and safe/captured. If a stone is not safe 
			it also adds constraints that the stone is captured ."""
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					#Cannot have both stone colours on same pos, cant have a safe stone be captured
					self.E.add_constraint(~(BlackOccupied(i, j) & WhiteOccupied(i, j)))
					self.E.add_constraint(~(Safe(i, j) & Captured(i, j))) 
					#If there is a liberty here make surrounding stones of any colour safe
					if not is_stone(i,j):
						safe(i,j,"any") #This then recursively reaches all connected stones
			#After safeties are calculated, add unsafe stones to captured
			for i in range(GRID_SIZE):
				for j in range(GRID_SIZE):
					#If a stone is not safe then it is captured
					if Safe(i, j) not in self.safe_stones:
						self.E.add_constraint(Captured(i, j))
						if WhiteOccupied(i, j) in self.wht_stones:
							self.cap_white_stones.add(Captured(i, j))
						elif BlackOccupied(i,j) in self.blk_stones:
							self.cap_black_stones.add(Captured(i, j))

		add_from_board(self.board)
		add_constraints()

		T = self.E.compile()

		# Checks for contradicting constraints
		satisfiable = T.satisfiable()

		return satisfiable

	def print_line(self, thin = False):
		"""Prints a large line if clear is False, and if clear
		is True, then prints a thin spaced line."""
		width = get_terminal_size().columns
		if thin:
				print("\r"+"─ "*(width//2)+"\n")
		else:
			print("━"*width)
	
	def print_progress(self, progress):
		"""Prints a progress bar to display how far through a 
		board the move lookahead is currently."""
		total_runtime = GRID_SIZE**2
		terminal_width = get_terminal_size().columns - 3
		progress_width = progress*terminal_width//total_runtime
		print("\r"+"["+"─"*progress_width+" "*(terminal_width-progress_width)+\
			"]",end="",flush=True)

	def print_stones(self, display_moves = []):
		"""Prints all of the stones from the board and whether they are captured or not.
		Needs to have the board populated. Can also display best move(s) in red."""
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
	
	def remove_captured_stones(self, first):
		""" Removes stones based on the colour described in 'first' 
		and reruns the board to see what stones of the opposite colour 
		are then considered taken. If first is 'any' then this rerun is 
		ignored and all captured stones are immediately removed."""
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

	def can_place(self, i, j):
		"""Checks if a stone is already in the board in position (i,j)."""
		if (i,j) in self.board["black"] or (i,j) in self.board["white"]:
			return False
		return True

	def check_valid_move(self, i, j, player_set, other_set):
		"""Checks if move at (i,j) by player in player_set is valid. 
		If the move is captured but the surrounding pieces in the other 
		colour are captured, then it is valid. If the move is not captured 
		it is automatically valid."""
		#If move is considered captured.
		if f"(i{i} j{j} C)" in player_set:
			for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]:
				if f"(i{i+di} j{j+dj} C)" in other_set:
					#If this move captures enemy's piece then it is okay
					return True
			return False
		else:
			return True
	
	def check_snapback(self, white_move, captured_white, i, j):
		"""Checks for snap back by seeing if a move for white 
		that captures more than one black piece was captured by 
		black's last move."""
		for b in range(len(white_move[2])):
			wi, wj = white_move[1][b]
			if f"(i{wi} j{wj} C)" in captured_white and white_move[0] > 1:
				#Changes stones to be the move after white for displaying purposes.
				#These are later overwritten.
				self.cap_black_stones = white_move[2][b]
				self.cap_white_stones = set()
				self.board["white"].add((wi,wj))
				self.print_line(True)
				print("Potential snapback found - Black move:", (i,j), 
		  			"White move:", white_move[1][b])
				self.print_stones()
	
	def next_black_move(self):
		"""Find the best possible black move(s) and their score, 
		considering the best possible move white could play to counter."""
		max_score = None
		black_stone_pos = [] #List of best black moves
		#Used for terminal progress bar
		progress = 0
		
		self.run()
		self.print_stones()
		
		#Remove already captured stones from both sides, starting with black
		self.remove_captured_stones("black")

		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				#Prints current progress in terminal window
				self.print_progress(progress)
				progress+=1

				if not self.can_place(i,j):
					continue
				
				#Create a backup of current board
				black = set(self.board["black"])
				white = set(self.board["white"])

				# we can add a black stone to the square
				self.board["black"].add((i,j))
				#Run test and see if the move is illegal
				satisfiable = self.run()
				satisfiable &= self.check_valid_move(i,j,
									player_set=self.cap_black_stones,
									other_set=self.cap_white_stones)

				if satisfiable:
					score = len(self.cap_white_stones)
					captured_white = set(self.cap_white_stones) # copy set
					
					#Remove captured stones after this turn starting with white
					self.remove_captured_stones("white")
					white_move = self.next_white_move()
					score -= white_move[0]
					
					#Checks for potential snapback
					self.check_snapback(white_move,captured_white, i,j)

					if max_score == None or score > max_score:
						max_score = score
						black_stone_pos = [(i,j)]
					elif score == max_score:
						black_stone_pos.append((i,j))
				
				#Reset board positions for next iteration
				self.board["black"] = black
				self.board["white"] = white
		self.print_line(thin=True)
		self.run() #Refresh board positions
		return max_score, black_stone_pos

	def next_white_move(self):
		"""Finds the best possible white move(s), their score,
		and the black stones they capture."""
		max_score = None
		white_stone_pos = [] #List of best white moves 
		black_cap = [] #All black pieces captured by best white move
		
		for i in range(GRID_SIZE):
			for j in range(GRID_SIZE):
				if not self.can_place(i,j):
					continue
				
				# we can safely test and add a white stone to the square
				self.board["white"].add((i,j))
				#Run test and see if the move is illegal
				satisfiable = self.run()
				satisfiable &= self.check_valid_move(i,j,
									player_set=self.cap_white_stones,
									other_set=self.cap_black_stones)

				if satisfiable:
					score = len(self.cap_black_stones)

					#See if move is the best move so far
					if max_score == None or score > max_score:
						max_score = score
						white_stone_pos = [(i,j)]
						black_cap = [set(self.cap_black_stones)]
					elif score == max_score:
						white_stone_pos.append((i,j))
						black_cap.append(set(self.cap_black_stones))
				
				#remove our tested white stone
				self.board["white"].remove((i,j))
		return max_score, white_stone_pos, black_cap
	
	def next_move(self):
		self.print_line()
		#Print test name
		print("Test:", self.description, "\n")

		output = self.next_black_move()
		if output[0] == None:
			print("No valid move can be played")
			return
		elif len(output[1]) > 1: 
			print("Best moves are:",output[1],"with score:", output[0], "(Note every best move is shown on the board)")
		else:
			print("Best move is:",output[1][0],"with score:", output[0])
		self.print_stones(output[1])
		
tests = [
	Test(
		'empty board',
		{
			"white": set(),
			"black": set(),
		}
	),
	Test(
		'single black stone',
		{
			"white": set(),
			"black": {(1,2)},
		}
	),
	Test(
		'single white stone',
		{
			"white": {(1,2)},
			"black": set(),
		}
	),
	Test(
		'single white stone surrounded by black',
		{
			"white": {(1,2)},
			"black": {(1,3),(0,2),(2,2),(1,1)},
		}
	),
	Test(
		'single white stone surrounded by 3 black',
		{
			"white": {(1,2)},
			"black": {(1,3),(2,2),(1,1)},
		}
	),      
	Test(
		'single white stone surrounded by 3 black one white',
		{
			"white": {(1,2),(0,2)},
			"black": {(1,3),(2,2),(1,1)},
		}
	),  
	Test(
		'complicated case, no liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (2,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		}
	),   
	Test(
		'complicated case, 2 liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		}
	), 
	Test(
		'full board white',
		{
			"white": {(i,j) for i in range(5) for j in range(5)},
			"black": set(),
		}
	), 

	Test(
		'full board white, two eyes',
		{
			"white": {(i,j) for i in range(5) for j in range(5) if (i,j) not in [(1,2),(4,0)]},
			"black": set(),
		}
	), 
	
	Test(
		'overlapping stones, not capturable',
		{
			"white": {(2,2)},
			"black": {(2,2)},
		}
	),
	Test(
		'overlapping stones',
		{
			"white": {(1,2)},
			"black": {(1,3),(0,2),(2,2),(1,1),(1,2)},
		}
	),
	Test(
		'overlapping stones, complicated case, no liberties',
		{
			"white": {(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)},
			"black": {(0,0), (2,0), (1,1), (3,1), (1,2), (1,3), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)},
		}
	),  
	Test(
			'half and half board',
			{
				"white": {(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)},
				"black": {(0,3),(0,4),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3),(4,4)},
			}
		),   
	Test(


            'Figure 2',
            {
                "white": {(2,1),(2,2),(2,3),(2,4),(2,0),(3,0),(3,2),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)},
                "black": {(0,3),(0,4),(1,3),(1,4),(2,4),(3,3),(3,4),(4,3),(4,4)},
            }
        ), 

    Test(


            'Figure 3',
            {
                "white": {(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)},
                "black": {(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4)},
            }
        ),

    Test(


            'Figure 4',
            {
                "white": {(2,1),(3,2),(1,2),(2,3)},
                "black": {(2,0),(3,1),(1,1),(0,2),(4,2),(1,3),(3,3),(2,4)},
            }
        ),
	Test(
        'Figure 5, Snap back position 1',
        {
            "white": {(1,0),(2,0),(3,0),(1,1),(1,2),(1,3),(1,4),(3,3),(4,1)},
            "black": {(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4),(4,2),(4,4)},
        },
    ),   
    
    Test(
        'Figure 6, Snap back position 2',
        {
            "white": {(1,0),(2,0),(3,1),(3,2),(3,3),(0,1),(1,2),(2,3)},
            "black": {(2,1),(1,1),(0,2),(0,3),(1,3)},
        },
    ),   

]

def run_tests():
	"""
	Run a list of board configurations and what they should evaluate to. Prints to console.
	"""
	for test in tests:
		test.next_move()

if __name__ == "__main__":
	run_tests()
