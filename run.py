from nnf import NNF
from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Encoding that will store all the constraints
E = Encoding()


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


def rotate_matrix_clockwise(matrix):
    """Rotates a given matrix clockwise"""
    new_matrix = []
    for y in range(len(matrix[0])):
        new_matrix.append([])
        for x in range(len(matrix)-1, -1, -1):
            new_matrix[y].append(matrix[x][y])
    return new_matrix


def print_all_solutions(model: NNF, bruteforce_allowance: int):
    """Prints every solution of the given model. bruteforce_allowance is the number of total solutions until the
    function should use model.models() to get all the solutions instead of bruteforcing them all with model.solve()"""
    num_solutions = count_solutions(model)

    if num_solutions <= bruteforce_allowance:
        solutions = []
        for i in range(num_solutions):
            solution = model.solve()
            while (solution in solutions):  # Keep finding solutions until it finds one that hasn't already been found.
                solution = model.solve()
            solutions.append(solution)
            print_grid(solution, cols, rows)
            print(f"Solution # {i + 1}/{num_solutions}")
            print("-------------------------")
    else:  # Use model.models() method once solution count gets large enough to make it worth it:
        solutions = model.models()
        i = 0
        for solution in solutions:
            i += 1
            print_grid(solution, cols, rows)
            print(f"Solution # {i}/{num_solutions}")
            print("-------------------------")

    # Count solutions:
    print(f"# Solutions: {num_solutions}")


def iff(a, b) -> NNF:
    """Iff helper function"""
    return (a & b) | (~a & ~b)


false = FalseProposition("false")
class BlackAndWhiteSquares:
    def __init__(self, cols, rows, board, line, only_solved):
        self.ROWS_TOTAL = rows * 2 + 1
        self.COLUMNS_TOTAL = cols * 2 + 1

        self.ROWS_TILES = rows
        self.COLUMNS_TILES = cols

        self.ROWS_POINTS = rows + 1
        self.COLUMNS_POINTS = cols + 1
        self.MAX_DIST = self.ROWS_POINTS*self.COLUMNS_POINTS

        self.board = board
        self.line = line
        self.only_solved = only_solved

        # Propositions
        self.q = BasicPropositions("q")  # True when drawn line is a valid solution

        self.w = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "w") # White square
        self.b = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "b") # Black square
        self.t = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "t") # Empty square
        self.j = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "j") # Black square is touching
        self.k = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "k") # White square is touching
        self.i = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "i") # Empty  touching a black square and a white square
        self.p = generate_2d_array(self.COLUMNS_TILES, self.ROWS_TILES, "p") # White touching a black square
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

        #   There can be at most one line with any given distance to the start.
        for i in range(self.MAX_DIST):
            constraint.add_at_most_one(E, *self.d[i])

        #   Static board configuration setup:
        do_static_board = True if self.board else False
        if do_static_board:
            s_x, s_y = self.board[0][0]
            e_x, e_y = self.board[0][1]
            E.add_constraint(self.s[s_x][s_y])
            E.add_constraint(self.e[e_x][e_y])
            del self.board[0]   #   Remove the start and end points from the board matrix.
            self.board = rotate_matrix_clockwise(self.board)    #   Rotate the board matrix so it matches the intended orientation.

        #   Only apply this constraint when not in the static board mode. This allows the static grid to have more than
        #   one empty tile, as long as the user doesn't put any empty tiles next to each other.
        else:
            #   There can be at most one empty space.
            constraint.add_at_most_one(E, *self.t)


        #   Static line configuration setup:
        do_static_line = True if self.line else False
        if do_static_line:
            E.add_constraint(self.s[self.line[0][0]][self.line[0][1]])
            E.add_constraint(self.e[self.line[-1][0]][self.line[-1][1]])
            for i in range(len(self.line)-1):
                x, y = self.line[i]
                next_x, next_y = self.line[i+1]
                E.add_constraint(self.l[x][y])
                if y < next_y and x == next_x: #   Connection up:
                    E.add_constraint(self.c[x][y][0])
                elif x < next_x and y == next_y: #   Connection right:
                    E.add_constraint(self.c[x][y][1])
                elif next_y < y and x == next_x: #   Connection down:
                    E.add_constraint(self.c[next_x][next_y][0])
                elif next_x < x and y == next_y: #   Connection left:
                    E.add_constraint(self.c[next_x][next_y][1])
                else:
                    raise Exception(f"Given static line is not contiguous. Assure each given coordinate only "
                                    "increases by 1 in EITHER the x or y axis from the previous coordinate.\n"
                                    f"Index {i}: ({x},{y}) -> ({next_x},{next_y})")
            E.add_constraint(self.l[self.line[-1][0]][self.line[-1][1]])


        #   Tile grid loop:
        empty_touching_bw = false   #   NNF to store if any empty tiles touching both black and white squares.
        white_touching_b = false    #   NNF to store if any white squares touching black squares.
        for x in range(self.COLUMNS_TILES):
            for y in range(self.ROWS_TILES):

                #   If in static board mode:
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

                #   A tile is empty if it doesn't contain a white or black square.
                #   t(x, y) ↔ ¬b(x, y) ∧ ¬w(x, y)
                E.add_constraint(iff(self.t[x][y], ~self.b[x][y] & ~self.w[x][y]))

                #   If there are any empty tiles touching both black and white squares:
                empty_touching_bw = empty_touching_bw | self.i[x][y]
                #   If there are any white squares touching black squares:
                white_touching_b = white_touching_b | self.p[x][y]

        #   A solution is only solved when no empty spaces are touching black and white squares,
        #   and no white squares are touching black squares.
        #   q ↔ ¬( i(0,0) ∨ i(1,0) ∨ i(2,0) ∨ … ∨ i(3,3) ) ∧ ¬( p(0,0) ∨ p(1,)0 ∨ p(2,0) ∨ … ∨ p(3,3) )
        E.add_constraint(iff(self.q, ~empty_touching_bw & ~white_touching_b))


        #   Point grid loop:
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
        if self.only_solved: E.add_constraint(self.q)

        return E

def print_grid(s: dict, cols: int, rows: int, print_if_solved = False):
    ROWS = rows * 2 + 1
    COLUMNS = cols * 2 + 1

    #   Create grid matrix with all items set as "   "
    grid = [["   " for j in range(ROWS)] for i in range(COLUMNS)]

    #   Iterate over the s dictionary:
    for key, value in s.items():

        prop = key.data[0]  # Get proposition type from dict s

        if print_if_solved and prop == "q":
            if value:
                print("SOLVED")
            else:
                print("NOT SOLVED")
            continue

        if len(key.data) <= 2:
            continue

        #   If the value of the proposition is true, modify the grid matrix:
        if value:

            #   Depending on the proposition type, replace the string in the grid matrix:
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

    #   Print the grid matrix:
    for y in range(ROWS-1, -1, -1):
        for x in range(COLUMNS):
            print(grid[x][y], end="")
        print()


def example_theory(cols = 3, rows = 3, board = None, line = None, only_solved=False):
    bws_class = BlackAndWhiteSquares(cols, rows, board, line, only_solved)
    return E


#   Main:
if __name__ == "__main__":
    mode = 0    #   <--------------- Change program mode here (0, 1, 2, or 3)

    #   Mode descriptions:
    mode_dict = {
        0 : "Find any valid board",
        1 : "Find any solved board",
        2 : "Static tiles",
        3 : "Static line"
    }
    print(f"Mode: {mode_dict[mode]}")

    #   Find any valid model, state if the board is solved:
    if mode == 0:
        #   Modify for different board sizes:
        cols = 3
        rows = 3

        T = example_theory(cols, rows)  #   Create theory.
        T = T.compile()    #    Compile theory.

        print("Satisfiable: %s\n" % T.satisfiable())
        solution = T.solve()
        if solution: print_grid(solution, cols, rows, print_if_solved=True)

        # Count solutions (Runs only if grid size is >= 2x2):
        if cols <= 2 and rows <= 2: print("# Solutions: %d" % count_solutions(T))


    #   Find any solved model:
    elif mode == 1:
        #   Modify for different board sizes:
        cols = 3
        rows = 3

        T = example_theory(cols, rows, only_solved=True)  #   Create theory.
        T = T.compile()    #    Compile theory.

        print("Satisfiable: %s\n" % T.satisfiable())
        solution = T.solve()
        if solution: print_grid(solution, cols, rows)

        # Count solutions (Runs only if grid size is <= 2x2):
        if cols <= 2 and rows <= 2: print("# Solutions: %d" % count_solutions(T))


    #   Solutions with static tiles:
    elif mode == 2:
        #   Do NOT modify board size in this mode. Should always be 3x3.
        cols = 3
        rows = 3

        #   Modify matrix for different static tile configurations:
        #   First tuple is starting point location
        #   Second tuple is ending point location
        board = [
            [(3,3), (0,0)],
            ["B", "W", "W"],
            ["B", "", "W"],
            ["B", "W", "W"]
        ]
        #   Be careful not to put two empty tiles next to directly each other.
        #   The constraints cannot properly check for squares of differing colours
        #   in the same section if there are any empty tiles touching one another.


        T = example_theory(cols, rows, board=board, only_solved=True)  #   Create theory.
        T = T.compile()    #    Compile theory.

        print("Satisfiable: %s\n" % T.satisfiable())

        #   Using T.models() to list all the solutions to the model is significantly slower
        #   when calculating all line configurations with a static board as compared to how
        #   fast it is when calculating all square configurations with a static line. Using
        #   the T.models() method probably wouldn't see any gains in speed until the total
        #   number of solutions reaches about 60.
        print_all_solutions(T, 60)


    #   Solutions with static line:
    elif mode == 3:
        #   Modify for different board sizes:
        cols = 3
        rows = 3

        #   Modify list of tuples to change the static line.
        #   List of points in order from the starting point to the ending point. Assumes the first point
        #   in the list is the starting point and the last point in the list is the ending point.
        line = [
            (3, 3),
            (3, 2),
            (2, 2),
            (2, 1),
            (2, 0),
            (1, 0),
            (1, 1),
            (0, 1),
            (0, 2),
            (1, 2),
            (1, 3)
        ]

        T = example_theory(cols, rows, line=line, only_solved=True)  #   Create theory.
        T = T.compile()    #    Compile theory.

        #   Only calculate if grid size doesn't exceed 4x4 (the model gets too complex to calculate):
        if cols <= 4 and rows <= 4:
            print("Satisfiable: %s\n" % T.satisfiable())

            #   model.models() method is much faster here than it is when listing all the possible
            #   line configurations, so the number of total solutions to make it worth it
            #   is much lower.
            print_all_solutions(T, 10)

    print()
