
from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()

class Hashable:
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

black_squares = {1:{(0,0), (2,0), (1,1), (3,1), (1,2), (4,2), (0,3), (4,3), (1,4), (2,4), (3,4)}}
white_squares = {1:{(1,0), (2,1), (2,2), (3,2), (1,3), (2,3), (3,3)}}
surrounded = []

# Different classes for propositions are useful because this allows for more dynamic constraint creation
# for propositions within that class. For example, you can enforce that "at least one" of the propositions
# that are instances of this class must be true by using a @constraint decorator.
# other options include: at most one, exactly one, at most k, and implies all.
# For a complete module reference, see https://bauhaus.readthedocs.io/en/latest/bauhaus.html
# @constraint.implies_all(E)
# @proposition(E)
# class FancyPropositions:

#     def __init__(self, data):
#         self.data = data

#     def __repr__(self):
#         return f"A.{self.data}"

GRID_SIZE = 5
blk_dots = []
wht_dots = []
oob_dots = []

# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def build_theory():
    
    example_game(1)
    for dot in blk_dots:
        i,j = dot.i,dot.j
        E.add_constraint(~(BlackOccupied(i,j) & WhiteOccupied(i,j)))
    for dot in oob_dots:
        i,j = dot.i, dot.j
        E.add_constraint(OutOfBounds(i,j)>>BlackOccupied(i,j))
    return E

def out_of_bounds(i, j):
    if (i < 0 or j < 0 or i >= GRID_SIZE or j >= GRID_SIZE):
        return True
    return False

def example_game(version):
    for i in range(-2,GRID_SIZE+2):
        for j in range(-2,GRID_SIZE+2):
            if out_of_bounds(i,j):
                E.add_constraint(OutOfBounds(f"i{i}",f"j{j}"))
                oob_dots.append(OutOfBounds(f"i{i}",f"j{j}"))
            else:
                if (i,j) in black_squares[version] or out_of_bounds(i,j):
                    E.add_constraint(BlackOccupied(f"i{i}",f"j{j}"))
                    blk_dots.append(BlackOccupied(f"i{i}",f"j{j}"))
                else:
                    E.add_constraint(~BlackOccupied(f"i{i}",f"j{j}"))
                if (i,j) in white_squares[version]:
                    E.add_constraint(WhiteOccupied(f"i{i}",f"j{j}"))
                else:
                    E.add_constraint(~WhiteOccupied(f"i{i}",f"j{j}"))
            
            

def example_theory():
    # Add custom constraints by creating formulas with the variables you created. 
    E.add_constraint((a | b) & ~x)
    # Implication
    E.add_constraint(y >> z)
    # Negate a formula
    E.add_constraint(~(x & y))
    # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    constraint.add_exactly_one(E, a, b, c)

    return E

def print_board(sol):
    for j in range(GRID_SIZE):
        out = ""
        for i in range(GRID_SIZE):
            if sol[BlackOccupied(f"i{i}",f"j{j}")]:
                out+="⚫"
            elif sol[WhiteOccupied(f"i{i}",f"j{j}")]:
                out+="⚪"
            else:
                out+="🟫"
        print(out)

if __name__ == "__main__":

    T = build_theory()
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
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
    
    #print(sol)
    print_board(sol)
