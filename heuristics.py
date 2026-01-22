# =============================
# Student Names:
# Group ID:
# Date:
# =============================
# CISC 352
# heuristics.py
# desc:
#


#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within
   the propagators

1. ord_dh (worth 0.25/3 points)
    - a Variable ordering heuristic that chooses the next Variable to be assigned 
      according to the Degree heuristic


2. ord_mv (worth 0.25/3 points)
    - a Variable ordering heuristic that chooses the next Variable to be assigned 
      according to the Minimum-Remaining-Value heuristic


var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable

    csp is a CSP object---the heuristic can use this to get access to the
    Variables and constraints of the problem. The assigned Variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''

def ord_dh(csp):
    ''' return next Variable to be assigned according to the Degree Heuristic '''
    # IMPLEMENT
    maxDeg = float('inf')
    unassigned = csp.get_all_unasgn_vars()
    selected = None
    for var in unassigned:
        degree = 0
        for cst in csp.get_cons_with_var(var):
            for val in cst.get_scope():
                if val != var and not val.is_assigned():
                    degree += 1
                    break  # Only count this constraint once
        if degree > maxDeg:
            maxDeg = degree
            selected = var
    return selected


def ord_mrv(csp):
    ''' return Variable to be assigned according to the Minimum Remaining Values heuristic '''
    # IMPLEMENT
    unassigned = csp.get_all_unasgn_vars()
    minVar = None
    minSize = float('inf')
    for var in unassigned:
        size = var.cur_domain_size()
        if size < minSize:
            minSize = size
            minVar = var
    return minVar
    
