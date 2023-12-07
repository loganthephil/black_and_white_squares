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
    def __lt__(self, other):
        self.data < other.data


@constraint.none_of(E)
@proposition(E)
class FalseProposition:
    def __init__(self, data):
        self.data = data
    def __repr__(self):
        return f"A.{self.data}"
    def __lt__(self, other):
        self.data < other.data


def generate_2d_array(columns, rows, data):
    array = []
    for i in range(columns):
        row = []
        for j in range(rows):
            row.append(BasicPropositions(f"{data}({i},{j})"))
        array.append(row)
    return array

def generate_3d_array(x, y, z, data):
    array = []
    for i in range(x):
        row = []
        for j in range(y):
            column = []
            for k in range(z):
                column.append(BasicPropositions(f"{data}({i},{j},{k})"))
            row.append(column)
        array.append(row)
    return array

def flip_coords(coords:tuple):
    return coords[1], coords[0]

def rotate_matrix_clockwise(matrix):
    new_matrix = []
    for y in range(len(matrix[0])):
        new_matrix.append([])
        for x in range(len(matrix)-1, -1, -1):
            new_matrix[y].append(matrix[x][y])
    return new_matrix


def iff(a, b) -> NNF:
    return (a & b) | (~a & ~b)

false = FalseProposition("false")
true = ~false

class BlackAndWhiteSquares:
    def __init__(self, cols, rows, board):
        self.ROWS_TOTAL = rows * 2 + 1
        self.COLUMNS_TOTAL = cols * 2 + 1

        self.ROWS_TILES = rows
        self.COLUMNS_TILES = cols

        self.ROWS_POINTS = rows + 1
        self.COLUMNS_POINTS = cols + 1
        self.MAX_DIST = self.ROWS_POINTS*self.COLUMNS_POINTS

        self.board = board

        # Propositions
        self.q = BasicPropositions("q")  # True when drawn line is a valid solution

        self.w = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "w") # White square
        self.b = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "b") # Black square
        self.t = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "t") # Empty square
        self.j = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "j") # Black square is touching
        self.k = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "k") # White square is touching
        self.i = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "i") # Empty  touching a black square and a white square
        self.p = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "p") # Touching a black square
        self.s = generate_2d_array(self.COLUMNS_POINTS, self.ROWS_POINTS, "s") # Starting point
        self.e = generate_2d_array(self.COLUMNS_POINTS, self.ROWS_POINTS, "e") # Ending point
        self.l = generate_2d_array(self.COLUMNS_POINTS, self.ROWS_POINTS, "l") # Line segment
        self.c = generate_3d_array(self.COLUMNS_POINTS, self.ROWS_POINTS, 2, "c") # Connected - z coordinate is direction of connection {0:up, 1:right}
        self.d = generate_3d_array(self.MAX_DIST, self.COLUMNS_POINTS, self.ROWS_POINTS, "d") # Distance

        self.build_constraints()




    def build_constraints(self):

        #   There can only ever be one starting and end point.
        constraint.add_exactly_one(E, *self.s)
        constraint.add_exactly_one(E, *self.e)

        #   There must always be at least one white and black square.
        constraint.add_at_least_one(E, *self.w)
        constraint.add_at_least_one(E, *self.b)

        #   There can be at most one empty space.
        constraint.add_at_most_one(E, *self.t)

        #   There can be at most one line with any given distance to the start.
        for i in range(self.MAX_DIST):
            constraint.add_at_most_one(E, *self.d[i])

        do_static_board = True if self.board else False
        if do_static_board:
            static_s = flip_coords(self.board[0][0])
            static_e = flip_coords(self.board[0][1])
            E.add_constraint(self.s[static_s[0]][static_s[1]])
            E.add_constraint(self.e[static_e[0]][static_e[1]])
            del self.board[0]
            self.board = rotate_matrix_clockwise(self.board)

        for x in range(self.COLUMNS_TILES):
            for y in range(self.ROWS_TILES):
                if do_static_board:
                    tile = self.board[x][y]
                    if tile == "W":
                        E.add_constraint(self.w[x][y])
                    elif tile == "B":
                        E.add_constraint(self.b[x][y])
                    else:
                        E.add_constraint(self.t[x][y])


                #   A square is “touching” a black square only when a black square is a single x or y coordinate
                #   away (no diagonals) and there is no connection between line segments between them.
                #   j(x,y) ↔ ( b(x,y+1) ∧ ¬c(x,y+1,1) ) ∨ ( b(x+1,y) ∧ ¬c(x+1,y,1) ) ∨ ( b(x,y-1) ∧ ¬c(x,y,1) ) ∨ ( b(x-1,y) ∧ ¬c(x,y,1) )
                up = self.b[x][y + 1] & ~self.c[x][y+1][1] if y + 1 < self.ROWS_TILES else false
                right = self.b[x + 1][y] & ~self.c[x+1][y][0] if x + 1 < self.COLUMNS_TILES else false
                down = self.b[x][y - 1] & ~self.c[x][y][1] if y - 1 >= 0 else false
                left = self.b[x - 1][y] & ~self.c[x][y][0] if x - 1 >= 0 else false
                E.add_constraint(iff(self.j[x][y], up | right | down | left))

                #   Same idea applies for white squares k(x,y).
                up = self.w[x][y + 1] & ~self.c[x][y+1][1] if y + 1 < self.ROWS_TILES else false
                right = self.w[x + 1][y] & ~self.c[x+1][y][0] if x + 1 < self.COLUMNS_TILES else false
                down = self.w[x][y - 1] & ~self.c[x][y][1] if y - 1 >= 0 else false
                left = self.w[x - 1][y] & ~self.c[x][y][0] if x - 1 >= 0 else false
                E.add_constraint(iff(self.k[x][y], up | right | down | left))

                #   An empty tile is only touching a black square and a white square when the tile has neither
                #   white nor black on it and the previous constraints for touching black and white squares are met.
                #   i(x,y) ↔ t(x,y) ∧ j(x,y) ∧ k(x,y)
                E.add_constraint(iff(self.i[x][y], self.t[x][y] & self.j[x][y] & self.k[x][y]))

                #   Similar idea applies for white squares touching blacks squares.
                #   p(x,y) ↔ w(x,y) ∧ j(x,y)
                E.add_constraint(iff(self.p[x][y], self.w[x][y] & self.j[x][y]))

                #   A square can be exclusively black or white, not both.
                #   ( w(x,y) → ¬ b(x,y) ) ∧ ( b(x,y) → ¬ w(x,y) )
                E.add_constraint((self.w[x][y] >> ~self.b[x][y]) & (self.b[x][y] >> ~self.w[x][y]))

                #   A solution is only solved when no empty spaces are touching black and white squares,
                #   and no white squares are touching black squares.
                #   q ↔ ¬( i(0,0) ∨ i(1,0) ∨ i(2,0) ∨ … ∨ i(3,3) ) ∧ ¬( p(0,0) ∨ p(1,)0 ∨ p(2,0) ∨ … ∨ p(3,3) )
                E.add_constraint(iff(self.q, ~self.i[x][y] & ~self.p[x][y]))

                #   A tile is empty if it doesn't contain a white or black square.
                #   t(x, y) ↔ ¬b(x, y) ∧ ¬w(x, y)
                E.add_constraint(iff(self.t[x][y], ~self.b[x][y] & ~self.w[x][y]))

        for x in range(self.COLUMNS_POINTS):
            for y in range(self.ROWS_POINTS):
                # A point can't be both the starting point and ending point.
                # ¬s(x,y) ∨ ¬e(x,y)
                E.add_constraint(~self.s[x][y] | ~self.e[x][y])

                # There must always be a line segment at the starting point, and ending point.
                #   s(x,y) → l(x,y)
                #   e(x,y) → l(x,y)
                E.add_constraint(self.s[x][y] >> self.l[x][y])
                E.add_constraint(self.e[x][y] >> self.l[x][y])

                #   A point cannot be connected to a non-existent point "out-of-bounds".
                #   ¬c(x,4,0)
                #   ¬c(4,y,1)
                if y + 1 >= self.ROWS_POINTS: E.add_constraint(~self.c[x][y][0])
                if x + 1 >= self.COLUMNS_POINTS: E.add_constraint(~self.c[x][y][1])

                #   A point being connected to another point implies that there is a line segment at both ends of the connection.
                if y + 1 < self.ROWS_POINTS: E.add_constraint(self.c[x][y][0] >> (self.l[x][y] & self.l[x][y+1]))
                if x + 1 < self.COLUMNS_POINTS: E.add_constraint(self.c[x][y][1] >> (self.l[x][y] & self.l[x+1][y]))

                #   Any point on the line that isn’t the start or end point must be connected to two other points of the line.
                #   In other words, the line must be a single continuous line from start to end without branching paths.
                up = self.c[x][y][0] if y + 1 < self.ROWS_POINTS else false
                right = self.c[x][y][1] if x + 1 < self.COLUMNS_POINTS else false
                down = self.c[x][y - 1][0] if y - 1 >= 0 else false
                left = self.c[x - 1][y][1] if x - 1 >= 0 else false
                one_connection = ((up & ~right & ~down & ~left) | (~up & right & ~down & ~left) |
                                  (~up & ~right & down & ~left) | (~up & ~right & ~down & left))

                two_connections = ((up & right & ~down & ~left) | (up & ~right & down & ~left) |
                                   (up & ~right & ~down & left) | (~up & right & down & ~left) |
                                   (~up & right & ~down & left) | (~up & ~right & down & left))
                E.add_constraint(self.l[x][y] >> (((self.s[x][y] | self.e[x][y]) & one_connection) |
                                 (~self.s[x][y] & ~self.e[x][y] & two_connections)))

                #   The distance to the starting point at start must 0.
                #   s(x,y) → d(x,y,0)
                E.add_constraint(self.s[x][y] >> self.d[0][x][y])

                #   At any line segment there must be another line segment connected
                #   with a distance less than the specified line segment.
                for i in range(1, self.MAX_DIST):
                    up = self.c[x][y][0] & self.d[i-1][x][y+1] if y + 1 < self.ROWS_POINTS else false
                    right = self.c[x][y][1] & self.d[i-1][x+1][y] if x + 1 < self.COLUMNS_POINTS else false
                    down = self.c[x][y-1][0] & self.d[i-1][x][y-1] if y - 1 >= 0 else false
                    left = self.c[x-1][y][1] & self.d[i-1][x-1][y] if x - 1 >= 0 else false
                    E.add_constraint(self.d[i][x][y] >> (up | right | down | left))

                #   Every point with a line segment must have a distance to the start.
                any_distance = false
                for i in range(self.MAX_DIST):
                    any_distance = any_distance | self.d[i][x][y]
                E.add_constraint(self.l[x][y] >> any_distance)

                #   Every point with a distance can only have one distance at that point.
                for i in range(self.MAX_DIST):
                    any_other_distance = false
                    for j in range(self.MAX_DIST):
                        if j != i: any_other_distance = any_other_distance | self.d[j][x][y]
                    E.add_constraint(self.d[i][x][y] >> ~any_other_distance)

        # The solution must be valid.
        E.add_constraint(self.q)

        return E

def print_grid(s: dict, cols: int, rows: int):
    ROWS = rows * 2 + 1
    COLUMNS = cols * 2 + 1

    grid = [["   " for j in range(ROWS)] for i in range(COLUMNS)]

    for key, value in s.items():
        if len(key.data) < 2:
            continue

        if value:

            prop = key.data[0]
            if prop == "":
                print(f"{key}")

            if prop != "d":
                x = int(key.data[2])
                y = int(key.data[4])
                if prop == "s":
                    grid[2 * x][2 * y] = " S "
                elif prop == "e":
                    grid[2 * x][2 * y] = " E "
                elif prop == "w":
                    grid[2 * x + 1][2 * y + 1] = " W "
                elif prop == "b":
                    grid[2 * x + 1][2 * y + 1] = " B "
                elif prop == "l" and grid[2 * x][2 * y] == "   ":
                    grid[2 * x][2 * y] = " * "
                elif prop == "c":
                    z = int(key.data[6])
                    if z == 1: grid[2 * x + 1][2 * y] = "---"
                    else: grid[2 * x][2 * y + 1] = " | "


    for y in range(ROWS-1, -1, -1):
        for x in range(COLUMNS):
            print(grid[x][y], end="")
        print()


#   Build an example full theory for your setting and return it.
#
#   There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#   This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#   what the expectations are.
def example_theory(cols = 3, rows = 3, board = None):
    bws_class = BlackAndWhiteSquares(cols, rows, board)
    return E


if __name__ == "__main__":
    mode = 1
    mode_dict = {
        0 : "Solved board",
        1 : "Possible lines"
    }
    print(f"Mode: {mode_dict[mode]}")

    # Find any solved model:
    if mode == 0:
        #   Modify for different board sizes:
        cols = 3
        rows = 3

        # T = example_theory(cols, rows)
        T = example_theory(cols, rows)
        # Don't compile until you're finished adding all your constraints!
        T = T.compile()
        # After compilation (and only after), you can check some of the properties
        # of your model:
        print("\nSatisfiable: %s" % T.satisfiable())
        solution = T.solve()
        # print("   Solution: %s" % solution)
        if solution: print_grid(solution, cols, rows)

        # Count solutions (Runs only if grid size is >= 2x2):
        if cols <= 2 and rows <= 2: print("# Solutions: %d" % count_solutions(T))

    # Solutions with static board:
    elif mode == 1:
        #   Do not modify board size in this mode.
        cols = 3
        rows = 3

        #   Modify matrix for different static board configurations:
        #   First tuple is starting point location
        #   Second tuple is ending point location
        board = [
            [(3,3), (1,0)],
            ["W", "W", "B"],
            ["W", "B", "W"],
            ["W", "B", "W"]
        ]


        T = example_theory(cols, rows, board)
        T = T.compile()

        print("\nSatisfiable: %s" % T.satisfiable())

        #   Seemingly inefficient way to list all the solutions to the board, but
        #   alternative of using T.models() was insanely slow in comparison:
        num_solutions = count_solutions(T)
        solutions = []
        for i in range(num_solutions):
            solution = T.solve()
            while (solution in solutions):
                solution = T.solve()
            solutions.append(solution)
            print_grid(solution, cols, rows)
            print(f"Solution # {i+1}/{num_solutions}")
            print("-------------------------")

        # Count solutions:
        print(f"# Solutions: {num_solutions}")


    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
