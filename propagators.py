# =============================
# Student Names: Elisa Goncalves, Gabrielle Garey
# Group ID: 22
# Date: Jan 16
# =============================
# CISC 352
# propagators.py
# desc:
#

from collections import deque


#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within
   bt_search.

    1. prop_FC (worth 0.5/3 marks)
        - a propagator function that propagates according to the FC algorithm that 
          check constraints that have exactly one Variable in their scope that has 
          not assigned with a value, and prune appropriately

    2. prop_GAC (worth 0.5/3 marks)
        - a propagator function that propagates according to the GAC algorithm, as 
          covered in lecture

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned Variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned Variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any Variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of Variable values pairs are all of the values
      the propagator pruned (using the Variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a Variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining Variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one Variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a Variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned Variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check_tuple(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated Variable. Remember to keep
       track of all pruned Variable,value pairs and return '''
    #IMPLEMENT
    
    # for forward checking (where we only check constraints with one 
    # remaining Variable) we look for unary constraints of the csp (constraints whose scope
    # contains only one Variable) and we forward_check these constraints.

    pruned_values = []
    
    if newVar is None:  # check all unary constraints
        constraints = csp.get_all_cons() 
    else:  # Check constraints involving newVar
        constraints = csp.get_cons_with_var(newVar)

    for cst in constraints:
        if cst.get_n_unasgn() == 1:
            unassigned_var = None
            for var in cst.get_scope(): # look at each var in list of vars involved in constraint
                if not var.is_assigned():
                    unassigned_var = var
                    break # stop searching bc we're looking for only one unassigned var
        
            for val in unassigned_var.cur_domain():
                tuples = [] # will reset each loop, should add (Variable, value) pairs for each var in scope
                for var in cst.get_scope():
                    if var.is_assigned():
                        tuples.append(var.get_assigned_value()) # assigned var
                    else:
                        tuples.append(val) # test val to see if constraint satis.
                
                # check_tuple : takes list of vals, returns True if constraints satisfied
                if not cst.check_tuple(tuples): # if the tuple not valid, prune 
                    if unassigned_var.in_cur_domain(val):  # if in_cur_domain = True: not pruned
                        unassigned_var.prune_value(val)
                        pruned_values.append((unassigned_var, val))
            
            if unassigned_var.cur_domain_size() == 0:
                return False, pruned_values
    
    return True, pruned_values


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT

    # scope: list of variables in the constraint's scope (ordered)
    # tup: tuple of values built so far (in scope order)

    def dfs(cst, scope, idx, tup):
        if idx == len(scope):
            # tuple is complete, check if it satisfies
            return cst.check_tuple(tup)
        var = scope[idx]
        if var in fixed:
            # If this variable is fixed, use its fixed value
            return dfs(cst, scope, idx + 1, tup + [fixed[var]])
        else:
            # Otherwise, try all values in the current domain
            for val in var.cur_domain():
                if dfs(cst, scope, idx + 1, tup + [val]):
                    return True
            return False

    pruned = []  

    if newVar is None:
        queue = [cst for cst in csp.get_all_cons() if cst.get_n_unasgn() > 0]
    else:
        queue = [cst for cst in csp.get_cons_with_var(newVar) if cst.get_n_unasgn() > 0]

    while queue:
        cst = queue.pop(0)
        for var in cst.get_scope():
            for val in list(var.cur_domain()):
                # Fix var to val for support like in cspbase, during DFS will always use test val instead of trying all possible values for var
                fixed = {var: val}
                # Check if there is any supporting tuple for var=val
                if not dfs(cst, cst.get_scope(), 0, []):
                    # No support: prune the value
                    var.prune_value(val)
                    pruned.append((var, val))

                    if var.cur_domain_size() == 0:
                        return False, pruned
                    
                    # Readd all related constraints (except current) to queue
                    for cst2 in csp.get_cons_with_var(var):
                        if cst2 != cst and cst2 not in queue:
                            queue.append(cst2)
    return True, pruned

"""
def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT

    def dfs(cst, tup, unassigned): # unassigned is a list
        if len(unassigned) == 0:
            return cst.check_tuple(tup)
`       
        unassigned_var = unassigned[0]
        # LOOP THRU DOMAIN of unassigned_var, add to temporary tuple, dfs on it
        for val in unassigned_var.cur_domain():
            copy_tup = tup.copy()
            copy_tup.append(val)

            if dfs(cst, copy_tup, unassigned[1:]):
                return True

        return False

    pruned_values = []
    
    queue = []

# LOOP through, and we're gonna check each constrainst 
    
    if newVar is None:
        queue = [x for x in csp.get_all_cons() if x.get_n_unasgn() > 0]
    
    else:
       queue = [x for x in csp.get_cons_with_var(newVar) if x.get_n_unasgn() > 0]
        
    # loop thru every constraint in queue
    for cst in queue:
        # another loop to get values at the constraints, if unassigned
        for var in cst.get_unasgn_vars():
            for val in var.cur_domain():
                var.assign(val)

                if not dfs(cst, [], cst.get_scope()):
                    var.prune_value(val)
                    pruned_values.append((var,val))
    
    # csp that doesn't have any unassgined
        if var.get_n_unasugn() == 0:
            return False, pruned_values
        
    # CSP that doesn't have any variables at all

        if var.cur_domain_size() == 0:
            return False, pruned_values

    return True, pruned_values
    """





        # need tuple of values that satisfy the constraint, list of unassigned



    

            




    
