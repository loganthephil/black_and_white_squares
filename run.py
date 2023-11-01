import nnf
from nnf import NNF
from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Different classes for propositions are useful because this allows for more dynamic constraint creation
# for propositions within that class. For example, you can enforce that "at least one" of the propositions
# that are instances of this class must be true by using a @constraint decorator.
# other options include: at most one, exactly one, at most k, and implies all.
# For a complete module reference, see https://bauhaus.readthedocs.io/en/latest/bauhaus.html

# Encoding that will store all the constraints
E = Encoding()

# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding
@proposition(E)
class BasicPropositions:
    def __init__(self, data):
        self.data = data
    def __repr__(self):
        return f"A.{self.data}"


@constraint.none_of(E)
@proposition(E)
class FalseProposition:
    def __init__(self, data):
        self.data = data
    def __repr__(self):
        return f"A.{self.data}"


def generate_2d_array(rows, columns, data):
    array = []
    for i in range(rows):
        row = []
        for j in range(columns):
            row.append(BasicPropositions(f"{data}({i},{j})"))
        array.append(row)
    return array

def iff(a, b) -> NNF:
    return (a & b) | (~a & ~b)

false = FalseProposition("false")
true = ~false

class BlackAndWhiteSquares:
    def __init__(self, rows, cols):
        self.ROWS = rows * 2 + 1
        self.COLUMNS = cols * 2 + 1

        # Propositions
        self.q = BasicPropositions("q")  # True when drawn line is a valid solution

        self.l = generate_2d_array(self.ROWS, self.COLUMNS, "l")
        self.w = generate_2d_array(self.ROWS, self.COLUMNS, "w")
        self.b = generate_2d_array(self.ROWS, self.COLUMNS, "b")
        self.t = generate_2d_array(self.ROWS, self.COLUMNS, "t")
        self.j = generate_2d_array(self.ROWS, self.COLUMNS, "j")
        self.k = generate_2d_array(self.ROWS, self.COLUMNS, "k")
        self.i = generate_2d_array(self.ROWS, self.COLUMNS, "i")
        self.p = generate_2d_array(self.ROWS, self.COLUMNS, "p")
        self.s = generate_2d_array(self.ROWS, self.COLUMNS, "s")
        self.e = generate_2d_array(self.ROWS, self.COLUMNS, "e")
        self.c = generate_2d_array(self.ROWS, self.COLUMNS, "c")

        self.build_constraints()


    def build_constraints(self):

        #   There can only ever be one starting and end point.
        constraint.add_exactly_one(E, *self.s)
        constraint.add_exactly_one(E, *self.e)

        constraint.add_at_least_one(E, *self.w)
        constraint.add_at_least_one(E, *self.b)

        constraint.add_at_most_one(E, *self.t)

        # Create variables to store NNF formulas that can be added to during the loop.
        empty_touching_both = false
        white_touching_black = false
        invalid_start = true
        invalid_end = true
        invalid_line = true
        for x in range(self.ROWS):
            for y in range(self.COLUMNS):
                #   A square is “touching” a black square only when a black square is two x or y coordinates
                #   away (no diagonals), and on the x or y coordinate between them there is no line segment.
                #   j(x,y) ↔ ( b(x,y+2) ∧ ¬l(x,y+1) ) ∨ ( b(x+2,y) ∧ ¬l(x+1,y) ) ∨ ( b(x,y-2) ∧  ¬l(x,y-1) ) ∨ ( b(x-2,y) ∧ ¬l(x-1,y) )
                up      = self.b[x][y+2] & ~self.l[x][y+1] if y + 2 < self.ROWS else false
                right   = self.b[x+2][y] & ~self.l[x+1][y] if x + 2 < self.COLUMNS else false
                down    = self.b[x][y-2] & ~self.l[x][y-1] if y - 2 >= 0 else false
                left    = self.b[x-2][y] & ~self.l[x-1][y] if x - 2 >= 0 else false
                E.add_constraint(iff(self.j[x][y], up | right | down | left))

                #   Same idea applies for white squares k(x,y).
                up      = self.w[x][y + 2] & ~self.l[x][y + 1] if y + 2 < self.ROWS else false
                right   = self.w[x + 2][y] & ~self.l[x + 1][y] if x + 2 < self.COLUMNS else false
                down    = self.w[x][y - 2] & ~self.l[x][y - 1] if y - 2 >= 0 else false
                left    = self.w[x - 2][y] & ~self.l[x - 1][y] if x - 2 >= 0 else false
                E.add_constraint(iff(self.k[x][y], up | right | down | left))

                #   An empty space is only touching a black square and a white square when the point has neither
                #   white nor black on it and the previous constraints for touching black and white squares are met.
                #   e(x,y) ↔ ( ¬b(x,y) ∧ ¬w(x,y) ) ∧ j(x,y) ∧ k(x,y)
                E.add_constraint(
                    iff(self.i[x][y], ~self.b[x][y] & ~self.w[x][y] & self.j[x][y] & self.k[x][y]))

                #   Similar idea applies for white squares touching blacks squares.
                #   p(x,y) ↔ ¬b(x,y) ∧ w(x,y) ∧ j(x,y)
                E.add_constraint(
                    iff(self.p[x][y], ~self.b[x][y] & self.w[x][y] & self.j[x][y]))

                # A square can be exclusively black or white, not both.
                # ( w(x,y) → ¬ b(x,y) ) ∧ ( b(x,y) → ¬ w(x,y) )
                E.add_constraint((self.w[x][y] >> ~self.b[x][y]) & (self.b[x][y] >> ~self.w[x][y]))

                # Any point on the line must either be on the starting
                # position or be on a valid grid space for a line segment.
                # l(x,y) → s(x,y) ∨ c(x,y)
                E.add_constraint(self.l[x][y] >> self.s[x][y] | self.c[x][y])

                # A grid space is a valid route for the line to take if the line
                # has somewhere to go after being added to the grid space.
                # if x%2==1:
                #     up      = false
                #     down    = false
                # else:
                #     up      = ~self.l[x][y + 1] if y + 1 < self.ROWS else false
                #     down    = ~self.l[x][y - 1] if y - 1 >= 0 else false
                # if y%2==1:
                #     right   = false
                #     left    = false
                # else:
                #     right   = ~self.l[x + 1][y] if x + 1 < self.COLUMNS else false
                #     left    = ~self.l[x - 1][y] if x - 1 >= 0 else false
                # E.add_constraint(self.c[x][y] >> up | right | down | left)

                # A grid space can’t be both the starting point and ending point.
                # ¬s(x,y) ∨ ¬e(x,y)
                E.add_constraint(~self.s[x][y] | ~self.e[x][y])

                # There must always be a line segment at the starting point, and ending point.
                E.add_constraint(self.s[x][y] >> self.l[x][y])
                E.add_constraint(self.e[x][y] >> self.l[x][y])

                # Any point on the line that isn’t the start or end point must be connected to two other points of the line.
                # In other words, the line must be a single continuous line from start to end without branching paths.
                up = self.l[x][y + 1] if y + 1 < self.ROWS else false
                right = self.l[x + 1][y] if x + 1 < self.COLUMNS else false
                down = self.l[x][y - 1] if y - 1 >= 0 else false
                left = self.l[x - 1][y] if x - 1 >= 0 else false
                one_connection =    ((up & ~right & ~down & ~left) | (~up & right & ~down & ~left) |
                                     (~up & ~right & down & ~left) | (~up & ~right & ~down & left))

                two_connections =   ((up & right & ~down & ~left) | (up & ~right & down & ~left) |
                                     (up & ~right & ~down & left) | (~up & right & down & ~left) |
                                     (~up & right & ~down & left) | (~up & ~right & down & left))
                E.add_constraint(self.l[x][y] >> ((self.s[x][y] | self.e[x][y]) & one_connection) |
                                 (~self.s[x][y] & ~self.e[x][y] & two_connections))

                # Add to variables storing NNF formulas for invalid start and end points.
                if (x%2==0 and y%2==1) or (x%2==1 and y%2==0) or (x%2==1 and y%2==1):
                    invalid_start = invalid_start & ~self.s[x][y]
                    invalid_end = invalid_end & ~self.e[x][y]

                # Add to variables storing NNF formulas:
                if x%2==1 and y%2==1: # Inside tile.
                    #print("RAN")
                    empty_touching_both = empty_touching_both | self.i[x][y]
                    white_touching_black = white_touching_black | self.p[x][y]
                    invalid_line = invalid_line & ~self.l[x][y]

                    # A grid space is empty if the space does not contain a white or black square.
                    E.add_constraint(iff(self.t[x][y], ~self.w[x][y] & ~self.b[x][y]))
                else: # Outside tile.
                    #   A grid space can only contain a white square if it is the inside of a tile.
                    #   ¬w(0,0) ∧ ¬w(0,1) ∧ … ∧ ¬w(0,6) ∧ ¬w(1,0) ∧ ¬w(1,2) ∧ ¬w(1,4) ∧ ¬w(1,6) ∧ … ∧ ¬w(6,6)
                    E.add_constraint(~self.w[x][y])

                    #   Same applies for black squares.
                    E.add_constraint(~self.b[x][y])

                    #   Same applies for empty tiles.
                    E.add_constraint(~self.t[x][y])

        #   A solution is only solved when no empty spaces are touching black and white squares,
        #   and no white squares are touching black squares:
        E.add_constraint(iff(self.q, ~empty_touching_both & ~white_touching_black))
        E.add_constraint(self.q)

        # The starting point must be on an "intersection" of the line area and cannot be within a tile.
        # ¬s(0,1) ∧ ¬s(0,3) ∧ ¬s(0,5) ∧ ¬s(1,0) ∧ ¬s(1,2) ∧ ¬s(1,4) ∧ ¬s(1,6) ∧ … ∧ ¬s(6,3) ∧ ¬s(6,5)
        E.add_constraint(invalid_start)
        # Same applies for the ending point.
        E.add_constraint(invalid_end)

        #   A line segment can never be on the inside of a tile.
        #   ¬l(1,1) ∧ ¬l(1,3) ∧ ¬l(1,5) ∧ ¬l(3,1) ∧ ¬l(3,3) ∧ ¬l(3,5) ∧ ¬l(5,1) ∧ ¬l(5,3) ∧ ¬l(5,5)
        E.add_constraint(invalid_line)

        return E

def print_grid(s: dict, rows, cols):
    ROWS = rows * 2 + 1
    COLUMNS = cols * 2 + 1

    grid = [["   " for j in range(COLUMNS)] for i in range(ROWS)]

    for key, value in s.items():
        if len(key.data) < 2:
            continue

        if value:
            # print(f"{key}: {value}")
            prop = key.data[0]
            x = int(key.data[2])
            y = int(key.data[4])
            if prop == "s":
                grid[x][y] = " S "
            elif prop == "e":
                grid[x][y] = " E "
            elif prop == "w":
                grid[x][y] = " W "
            elif prop == "b":
                grid[x][y] = " B "
            elif prop == "l" and grid[x][y] == "   ":
                if x%2 == 0 and y%2 == 1: grid[x][y] = " | "
                elif x%2 == 1 and y%2 == 0: grid[x][y] = "---"
                else: grid[x][y] = " * "

    for y in range(ROWS):
        for x in range(COLUMNS):
            print(grid[x][y], end="")
        print()




# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def example_theory(rows = 3, cols = 3):
    bws_class = BlackAndWhiteSquares(rows, cols)
    return E


if __name__ == "__main__":
    rows = 3
    cols = 3

    T = example_theory(3, 3)
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    solution = T.solve()
    #print("   Solution: %s" % solution)
    print_grid(solution, rows, cols)

    # DECREASE GRID SIZE BEFORE RUNNING
    #print("# Solutions: %d" % count_solutions(T))


    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
