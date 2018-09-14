from z3 import *

def is_number(s):
    try:
        float(s.numerator_as_long())
        return True
    except AttributeError:
        return False

def add_assertion(solv, var, expression):
    solv.assert_and_track(eval(expression), var)
    return 

def get_maximal(solv, unsatcore, list_vars):
    # solv is a solver with all hard constraints
    # unsat core is a set of soft predicates
    # list_vars is a list of names of all soft predicates
    curr = []
    current_max_set = []

    for var in list_vars:
        if (var not in unsatcore):
            F = eval(dict[var])
            solv.add(F)
            curr.append(var)
    result = solv.check()

    current_max_set = curr[:]
    current_model = solv.model()

    for pred in unsatcore:
        F = eval(dict[pred])
        solv.add(F)
        solv.push()
        result = solv.check()
        if (result == z3.sat):
            current_max_set.append(pred)
            current_model = solv.model()
        else:
            solv.pop()
    return [current_max_set, current_model]


# here is the node names mapping to variables

# v0: ATM fraud
# v1: Access ATM to prepare attack
# v2: Breaking into facility
# v3: Social engineering facility staff
# v4: Execute attacks on ATM
# v5: Transaction Reversal
# v6: Get user's credentials
# v7: Get PIN
# v8: Shoulder surf
# v9: Installing camera
# v10: Install EPP
# v11: Get card
# v12: Card Skimming
# v13: Install skimmer
# v14: Clone card
# v15: take card physically
# v16: Card Trapping
# v17: Steal card
# v18: Social Engineering card owner
# v19: Cash Trapping

v0= Real('v0')
v1= Real('v1')
v2= Real('v2')
v3= Real('v3')
v4= Real('v4')
v5= Real('v5')
v6= Real('v6')
v7= Real('v7')
v8= Real('v8')
v9= Real('v9')
v10= Real('v10')
v11= Real('v11')
v12= Real('v12')
v13= Real('v13')
v14= Real('v14')
v15= Real('v15')
v16= Real('v16')
v17= Real('v17')
v18= Real('v18')
v19= Real('v19')

t = Then('simplify', 'qfnra-nlsat')
s = t.solver()
s1 = t.solver()

s.set(unsat_core=True)
s1.set(unsat_core=True)

s.add(v0>=0, v0<=1)
s.add(v1>=0, v1<=1)
s.add(v2>=0, v2<=1)
s.add(v3>=0, v3<=1)
s.add(v4>=0, v4<=1)
s.add(v5>=0, v5<=1)
s.add(v6>=0, v6<=1)
s.add(v7>=0, v7<=1)
s.add(v8>=0, v8<=1)
s.add(v9>=0, v9<=1)
s.add(v10>=0, v10<=1)
s.add(v11>=0, v11<=1)
s.add(v12>=0, v12<=1)
s.add(v13>=0, v13<=1)
s.add(v14>=0, v14<=1)
s.add(v15>=0, v15<=1)
s.add(v16>=0, v16<=1)
s.add(v17>=0, v17<=1)
s.add(v18>=0, v18<=1)
s.add(v19>=0, v19<=1)
s.add(v0==v1*v4)
s.add(v4==(v5+v6+v19)-(v5*v6+v5*v19+v6*v19)+(v5*v6*v19))
s.add(v6==v7*v11)
s.add(v11==(v12+v15+v18)-(v12*v15+v12*v18+v15*v18)+(v12*v15*v18))
s.add(v15==(v16+v17)-(v16*v17))
s.add(v12==v13*v14)
s.add(v7==(v8+v9+v10)-(v8*v9+v8*v10+v9*v10)+(v8*v9*v10))
s.add(v1==(v2+v3)-(v2*v3))

s1.add(s.assertions())

# here come constraints on values defined in the attack tree file 

v0_pred = Bool('v0_pred')
s.assert_and_track(v0==0.0046, v0_pred)

v19_pred = Bool('v19_pred')
s.assert_and_track(v19==0.015, v19_pred)

v16_pred = Bool('v16_pred')
s.assert_and_track(v16==0.0094, v16_pred)

v12_pred = Bool('v12_pred')
s.assert_and_track(v12==0.0172, v12_pred)

v5_pred = Bool('v5_pred')
s.assert_and_track(v5==0.0038, v5_pred)


# Add your own soft constraints here.

# Template for new constraint:
# p = Bool(p)
# s.assert_and_track(v0 > v1, p)

x1 = Bool('x1')
x2 = Bool('x2')
x3 = Bool('x3')
x4 = Bool('x4')
x5 = Bool('x5')
x6 = Bool('x6')
x7 = Bool('x7')
s.assert_and_track(v12>v15, x1)
s.assert_and_track(v6>v19, x2)
s.assert_and_track(v19>v5, x3)
s.assert_and_track(v8>v9, x4)
s.assert_and_track(v9==v10, x5)
s.assert_and_track(v10==v13, x6)
s.assert_and_track(v16==v19, x7)

# Please also add the newly declrared name of the predicate and the predicate string expression to the dictionary dict below
dict = {v12_pred: "v12==0.0172", v19_pred: "v19==0.015", v16_pred: "v16==0.0094", v5_pred: "v5==0.0038", v0_pred: "v0==0.0046", x1: 'v12 > v15',
x2: 'v6 > v19', x3: 'v19>v5', x4: 'v8 > v9', x5: 'v9==v10', x6: 'v10==v13', x7: 'v16==v19'}
list_vars = list(dict.keys())


# Now Z3 checks satisfiability.
print 'You can find the mapping of variables to tree nodes in the Z3 input python file.'
result = s.check()
print result

if result == z3.sat:
    m = s.model()
    for d in m.decls(): 
        if (is_number(m[d])):
            print "%s = %s" % (d.name(), float(m[d].numerator_as_long())/float(m[d].denominator_as_long()))
        else:
            print "%s = %s" % (d.name(), m[d])
elif result == z3.unsat:
    print  "The problem is unsatisfiable, here is an unsat core found by Z3 (not guaranteed to be minimum):"
    c = s.unsat_core()
    print c
    print "You can try to experiment with removing some less important unsat core predicates, but this is not guaranteed to provide a maximal solution."
    max_sol = get_maximal(s1, c, list_vars)
    print "Here is a maximal satisfiable subset of soft predicates: %s " % (max_sol[0]) 
    print "A solution that satisifes this maximal subset is:"
    m = max_sol[1]
    for d in m.decls():
        if (is_number(m[d])):
            print "%s = %s" % (d.name(), float(m[d].numerator_as_long())/float(m[d].denominator_as_long()))
        else:
            print "%s = %s" % (d.name(), m[d])
elif result == z3.unknown:
    print "Too complex problem to solve for Z3, for this reason:"
    print s.reason_unknown()
    print "You can try to remove some non-linear constraints or simplify them"
else:
    print "Something went wrong"
    print "Please check the results of the solver"
