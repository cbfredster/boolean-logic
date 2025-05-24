# extra function for unit prop and branching sat to save writing within these function
def satisfies(clause_set, assignment):
        for i in clause_set:
            clause = False
            for l in i:
                if l in assignment:
                    clause = True
                    break
            if clause == False:
                return False
        return True
    
def PLelimination(clause_set):
    while True:
    
        pureliterals = []
        
        for c in clause_set:
            for l in c:
              if -l not in pureliterals:
                if l not in pureliterals:
                    pureliterals.append(l)

        for l in pureliterals:
            secondaryClause = []
            for c in clause_set:
                if l not in c:
                    secondaryClause.append(c)
            clause_set = secondaryClause
               
        unitClauses = []  
        for C in clause_set:
            if len(C) == 1: # checking for arrays of size 1 for unit clauses
                unitClauses.append(C[0])  
        
        if len(unitClauses) == 0:
            break #case where unit prop. cannot occur 
        
        for i in range(len(unitClauses)):
         for j in range(len(unitClauses)):
          if unitClauses[i] == -unitClauses[j]:     
            return clause_set
        
        for l in unitClauses:
            newClauses = [] #acts to store clauses once UP has been performed
            for C in clause_set:
                if l in C:  
                   continue
                
                if -l in C:
                 C.remove(-l)
                 
                newClauses.append(C)
                
            clause_set = newClauses  
            
    return clause_set

############################



def load_dimacs(file_name):
    clauseArray = []  
    with open(file_name, "r") as theDimacFile:
        for line in theDimacFile:
            if line.startswith('p') or line.startswith('c'):
                continue 
            
            uniqueClause = [] 
            for i in line.split(): 
                if i == '0':  
                    continue
                else:
                    uniqueClause.append(int(i))  
            
            clauseArray.append(uniqueClause) 
    return clauseArray



def simple_sat_solve(clause_set):
    variables = []  
    for c in clause_set:
        for l in c:
            absoluteliteral = abs(l)  
            if absoluteliteral not in variables: 
                variables.append(absoluteliteral)  

    pc = []  
    length = len(variables)
    
    for i in range(2 ** length):  # 2^n combinations as binary choice (true or false) for the variable count 'n'
        combination = []  # Initialized
        for j in range(length): 
            if i % 2 == 1:
                combination.append(True) 
            else:
                combination.append(False) 
            i = i // 2  
        pc.append(combination)

    
    for combination in pc:
        A = [None] * length 
        for i in range(length):
            A[i] = combination[i]  
        
        translated_assignment = []
        for e in range(len(variables)):
            if A[e]:
                translated_assignment.append(variables[e])  
            else:
                translated_assignment.append(-variables[e]) 
        
        if satisfies(clause_set, translated_assignment):
            return translated_assignment

    return False

def unit_propagate(clause_set):
    while True:
        unitClauses = []  
        
        for C in clause_set:
            if len(C) == 1: # checking for arrays of size 1 for unit clauses
                unitClauses.append(C[0])  
        
        if len(unitClauses) == 0:
            break #case where unit prop. cannot occur 
        
        for i in range(len(unitClauses)):
         for j in range(len(unitClauses)):
          if unitClauses[i] == -unitClauses[j]:     
            return clause_set
        
        for l in unitClauses:
            newClauses = [] #acts to store clauses once UP has been performed
            for C in clause_set:
                if l in C:  
                   continue
                
                if -l in C:
                 C.remove(-l)
                 
                newClauses.append(C)
                
            clause_set = newClauses  
            
    return clause_set


def branching_sat_solve(clause_set, partial_assignment):
    clause_set = unit_propagate(clause_set) #simplifies clause set if containing unit clauses and checks unsatisfiabiity
    pAssignments = []
    allvariables = []
    
    for i in partial_assignment:
        absolutePA = abs(i)
        if absolutePA not in pAssignments:  
            pAssignments.append(absolutePA) #craetes the array for partial assignments

    for eachArray in clause_set:
        for i in eachArray:
            absoluteliteral = abs(i)
            if absoluteliteral not in allvariables:  
                allvariables.append(absoluteliteral)

    if len(pAssignments) == len(allvariables): #if partial assignments equal number of variables then only two checks needed [special case]
        if satisfies(clause_set, partial_assignment):
            return partial_assignment #solution is the "partial" assignment
        else:
            return False

    Uvariable = None
    for i in clause_set:
        for e in i:
            v = abs(e)
            if v not in pAssignments:
                Uvariable = v
                break
        if Uvariable is not None:
            break
    if Uvariable is None:
        return False

   #recursive part
    PAtrue = partial_assignment + [Uvariable] 
    truesolution = branching_sat_solve(clause_set, PAtrue)
    if truesolution:
     return truesolution

    PAfalse = partial_assignment + [-Uvariable] 
    falsesolution = branching_sat_solve(clause_set, PAfalse)
    if falsesolution:
        return falsesolution

    #if neither true or flse subsitution works then no soultion, so unsatisified
    return False


def dpll_sat_solve(clause_set, partial_assignment):
    clause_set = PLelimination(clause_set) #simplifies clause set if containing unit clauses and checks unsatisfiabiity
    pAssignments = []
    allvariables = []
    
    for i in partial_assignment:
        absolutePA = abs(i)
        if absolutePA not in pAssignments:  
            pAssignments.append(absolutePA) #craetes the array for partial assignments

    for eachArray in clause_set:
        for i in eachArray:
            absoluteliteral = abs(i)
            if absoluteliteral not in allvariables:  
                allvariables.append(absoluteliteral)

    if len(pAssignments) == len(allvariables): #if partial assignments equal number of variables then only two checks needed [special case]
        if satisfies(clause_set, partial_assignment):
            return partial_assignment #solution is the "partial" assignment
        else:
            return False

    Uvariable = None
    for i in clause_set:
        for e in i:
            v = abs(e)
            if v not in pAssignments:
                Uvariable = v
                break
        if Uvariable is not None:
            break
    if Uvariable is None:
        return False

   #recursive part
    PAtrue = partial_assignment + [Uvariable] 
    truesolution = dpll_sat_solve(clause_set, PAtrue)
    if truesolution:
     return truesolution

    PAfalse = partial_assignment + [-Uvariable] 
    falsesolution = dpll_sat_solve(clause_set, PAfalse)
    if falsesolution:
        return falsesolution

    #if neither true or flse subsitution works then no soultion, so unsatisified
    return False


def test():
    print("Testing load_dimacs")
    try:
        dimacs = load_dimacs("sat.txt")
        assert dimacs == [[1],[1,-1],[-1,-2]]
        print("Test passed")
    except:
        print("Failed to correctly load DIMACS file")

    print("Testing simple_sat_solve")
    try:
        sat1 = [[1],[1,-1],[-1,-2]]
        check = simple_sat_solve(sat1)
        assert check == [1,-2] or check == [-2,1]
        print("Test (SAT) passed")
    except:
        print("simple_sat_solve did not work correctly a sat instance")

    try:
        unsat1 = [[1, -2], [-1, 2], [-1, -2], [1, 2]]
        check = simple_sat_solve(unsat1)
        assert (not check)
        print("Test (UNSAT) passed")
    except:
        print("simple_sat_solve did not work correctly an unsat instance")

    print("Testing branching_sat_solve")
    try:
        sat1 = [[1],[1,-1],[-1,-2]]
        check = branching_sat_solve(sat1,[])
        assert check == [1,-2] or check == [-2,1]
        print("Test (SAT) passed")
    except:
        print("branching_sat_solve did not work correctly a sat instance")

    try:
        unsat1 = [[1, -2], [-1, 2], [-1, -2], [1, 2]]
        check = branching_sat_solve(unsat1,[])
        assert (not check)
        print("Test (UNSAT) passed")
    except:
        print("branching_sat_solve did not work correctly an unsat instance")


    print("Testing unit_propagate")
    try:
        clause_set = [[1],[-1,2]]
        check = unit_propagate(clause_set)
        assert check == []
        print("Test passed")
    except:
        print("unit_propagate did not work correctly")


    print("Testing DPLL") #Note, this requires load_dimacs to work correctly
    problem_names = ["sat.txt","unsat.txt"]
    for problem in problem_names:
        try:
            clause_set = load_dimacs(problem)
            check = dpll_sat_solve(clause_set,[])
            if problem == problem_names[1]:
                assert (not check)
                print("Test (UNSAT) passed")
            else:
                assert check == [1,-2] or check == [-2,1]
                print("Test (SAT) passed")
        except:
            print("Failed problem " + str(problem))
    print("Finished tests")
