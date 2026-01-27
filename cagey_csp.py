# =============================
# Student Names:
# Group ID:
# Date:
# =============================
# CISC 352
# cagey_csp.py
# desc:
#

#Look for #IMPLEMENT tags in this file.
from itertools import permutations
'''
All models need to return a CSP object, and a list of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, varArr = binary_ne_grid(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

varArr is a list of all Variables in the given csp. If you are returning an entire grid's worth of Variables
they should be arranged linearly, where index 0 represents the top left grid cell, index n-1 represents
the top right grid cell, and index (n^2)-1 represents the bottom right grid cell. Any additional Variables you use
should fall after that (i.e., the cage operand variables, if required).

1. binary_ne_grid (worth 0.25/3 marks)
    - A model of a Cagey grid (without cage constraints) built using only
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 0.25/3 marks)
    - A model of a Cagey grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints.

3. cagey_csp_model (worth 0.5/3 marks)
    - a model of a Cagey grid built using your choice of (1) binary not-equal, or
      (2) n-ary all-different constraints for the grid, together with Cagey cage
      constraints.


Cagey Grids are addressed as follows (top number represents how the grid cells are adressed in grid definition tuple);
(bottom number represents where the cell would fall in the varArr):
+-------+-------+-------+-------+
|  1,1  |  1,2  |  ...  |  1,n  |
|       |       |       |       |
|   0   |   1   |       |  n-1  |
+-------+-------+-------+-------+
|  2,1  |  2,2  |  ...  |  2,n  |
|       |       |       |       |
|   n   |  n+1  |       | 2n-1  |
+-------+-------+-------+-------+
|  ...  |  ...  |  ...  |  ...  |
|       |       |       |       |
|       |       |       |       |
+-------+-------+-------+-------+
|  n,1  |  n,2  |  ...  |  n,n  |
|       |       |       |       |
| n^2-n | n^2-n |       | n^2-1 |
+-------+-------+-------+-------+

Boards are given in the following format:
(n, [cages])

n - is the size of the grid,
cages - is a list of tuples defining all cage constraints on a given grid.


each cage has the following structure
(v, [c1, c2, ..., cm], op)

v - the value of the cage.
[c1, c2, ..., cm] - is a list containing the address of each grid-cell which goes into the cage (e.g [(1,2), (1,1)])
op - a flag containing the operation used in the cage (None if unknown)
      - '+' for addition
      - '-' for subtraction
      - '*' for multiplication
      - '/' for division
      - '%' for modular addition
      - '?' for unknown/no operation given

An example of a 3x3 puzzle would be defined as:
(3, [(3,[(1,1), (2,1)],"+"),(1, [(1,2)], '?'), (8, [(1,3), (2,3), (2,2)], "+"), (3, [(3,1)], '?'), (3, [(3,2), (3,3)], "+")])

'''

from cspbase import *

def binary_ne_grid(cagey_grid):

    ##IMPLEMENT
    # vars = grid cells (r0w,col)
    # constraints: for each row, check it's not equal to a cell in another row (r,1) != (r,2)
    # ^ same for columns
    # top number: (row, col)
    # bottom number: varArr indices

    n = cagey_grid[0]
    csp = CSP("binary_ne_grid")

    # vars for each cell 
    varArr = []
    for r in range(n):
        row = []
        for c in range(n):
            var = Variable(f"Cell({r},{c})", list(range(1, n+1))) # needs name + scope
            csp.add_var(var)
            row.append(var)
        varArr.append(row)
    
    for r in range(n):
        for c in range(n):
            # Row constraints
            for k in range(c+1, n): # cell position
                con = Constraint(f"R{r}:C{c}!=C{k}", [varArr[r][c], varArr[r][k]])
                sat_tuples = []
                for val1 in range(1, n+ 1):
                    for val2 in range(1, n+1):
                        if val1 != val2:
                            sat_tuples.append((val1, val2))
                con.add_satisfying_tuples(sat_tuples)
                csp.add_constraint(con)
            
            # Col constraints
            for k in range(r+1, n):
                con = Constraint(f"C{c}:R{r}!=R{k}", [varArr[r][c], varArr[k][c]])
                sat_tuples = []
                for val1 in range(1, n+1):
                    for val2 in range(1, n+1):
                        if val1 != val2:
                            sat_tuples.append((val1, val2))
                con.add_satisfying_tuples(sat_tuples)
                csp.add_constraint(con)
    
    return csp, varArr

def nary_ad_grid(cagey_grid):
    ## IMPLEMENT
    n = cagey_grid[0]
    csp = CSP("nary_ad_grid")

    # vars for each cell 
    varArr = []
    for r in range(n):
        row = []
        for c in range(n):
            var = Variable(f"Cell({r},{c})", list(range(1, n+1))) # needs name + scope
            csp.add_var(var)
            row.append(var)
        varArr.append(row)

    # n-ary all-different constraints for each row
    for i in range(n):
        row_vars = [varArr[i][j] for j in range(n)]
        con = Constraint(f"Row{i}_AllDiff", row_vars)
        
        # need permutations where all values are different in row
        sat_tuples = []
        for perm in permutations(range(1, n+1)): # ex for n = 3: perm is [(1,2,3), (1,3,2), (2,1,3), (2,3,1), (3,1,2), (3,2,1)]
            sat_tuples.append(perm)
        con.add_satisfying_tuples(sat_tuples)
        csp.add_constraint(con)
    
    # do same for col
    for j in range(n):
        col_vars = [varArr[i][j] for i in range(n)]
        con = Constraint(f"Col{j}_AllDiff", col_vars)
        sat_tuples = []

        for perm in permutations(range(1, n+1)): #n! perms
            sat_tuples.append(perm)
        
        con.add_satisfying_tuples(sat_tuples)
        csp.add_constraint(con)
    
    return csp, varArr
    



def check_operation(values, expected, operation):
    if operation == "+":
        return sum(values) == expected
        
    elif operation == "*":
        product = 1
        for val in values:
            product *= val
        return product == expected
        
    elif operation == "-":
        sorted_vals = sorted(values, reverse=True)
        result = sorted_vals[0] - sum(sorted_vals[1:])
        return result == expected
    
    elif operation == "/":
        for perm in permutations(values):
            result = perm[0]
            for v in perm[1:]:
                result = result / v
            if result == expected:
                return True
        return False
    
    elif operation == "%":
        for perm in permutations(values):
            divisor = perm[0]
            res = sum(perm[1:])
            if res % divisor == expected: # if any perm works we can return true
                return True
        return False
    
    elif operation == '?':
        return (check_operation(values, expected, '+') or
                check_operation(values, expected, '-') or
                check_operation(values, expected, '*') or
                check_operation(values, expected, '/') or
                check_operation(values, expected, '%'))
    
    return False

def cagey_csp_model(cagey_grid):
    from itertools import product # for tuples

    # IMPLEMENT
    n, cages = cagey_grid

    #  nary_ad_grid
    csp, grid2d = nary_ad_grid(cagey_grid)   # grid2d is n^2 list of Variables

    # var_array: first n^2 grid cells
    var_array = []
    for r in range(n):
        for c in range(n):
            var_array.append(grid2d[r][c])

    # add cage op variables and cage constraints
    for (expected, cells, op) in cages:
        # cell variables for this cage, in given order
        cageVars = [grid2d[r-1][c-1] for (r, c) in cells]

        # String part used in the operator variable's name, e.g.
        # "Var-Cell(1,1), Var-Cell(1,2), Var-Cell(2,1), Var-Cell(2,2)"
        cell_name_strs = [f"Var-Cell({r},{c})" for (r, c) in cells]
        cell_name_part = ", ".join(cell_name_strs)

        # operator var name needs to match expected
        op_name = f"Cage_op({expected}:{op}:[{cell_name_part}])"

        
        """
        test_cages_1_correct:
        scope0 = [Variable("Cage_op(4:+:[Var-Cell11, Var-Cell12, Var-Cell21, Var-Cell22])", 
                   ['+', '-', '/', '*', 'f']),  # <-- 'f' is in the domain
         
        con0.add_satisfying_tuples([('+', 1, 1, 1, 1)])  # <-- 'f' never appears here
        """

        # operator domain: reference uses an 'f' dummy value, and '%' when needed (look at answer_set.py)
        # test val f in domain but not in sat_tuples
        if op in ('%', '?'):
            # modulo only appears in some puzzles so not valid for all (check answer set)
            op_domain = ['+', '-', '/', '*', '%', 'f']
        else:
            op_domain = ['+', '-', '/', '*', 'f']

        opVar = Variable(op_name, op_domain)
        csp.add_var(opVar)
        var_array.append(opVar)

        # cst: operator first, then cell vars
        con_name = f"Cage({expected}:{op}:[{cell_name_part}])"
        scope = [opVar] + cageVars
        con = Constraint(con_name, scope)

        # build satisfying tuples 
        sat_tuples = []

        if op == '?':
        # Unknown: accept any real op (+,-,*,/,%) that makes expected true

            for vals in product(*([range(1, n+1)] * len(cells))): # one range per cell
                # * for passing each element as diff argument: ex: lst = [A, B, C] -> f(*lst) same as f(A,B,C)
                # then product will generate cartesian product of each cage constraint (every possible assignment)
                for real_op in ['+', '-', '*', '/', '%']:
                    if check_operation(vals, expected, real_op):
                        sat_tuples.append((real_op,) + vals)
        else:
            for vals in product(*([range(1, n+1)] * len(cells))):
                if check_operation(vals, expected, op):
                    sat_tuples.append((op,) + vals)

        con.add_satisfying_tuples(sat_tuples)
        csp.add_constraint(con)

    return csp, var_array