from scipy.optimize import basinhopping, differential_evolution, minimize, least_squares
import numpy as np
import sys
import xml.etree.ElementTree as ET

index = 0
opt_var = {}
opt_var_inv = {}
hard_pred_str = []
distance_func_parts = []

def printOut(x):
    global opt_var_inv
    if len(x) <> len(opt_var_inv):
        print("[ERROR]: Results and node labels do not match")
        return
    for i in xrange(len(x)):
        print(opt_var_inv[i], "{0:.4f}".format(x[i]))

def processSoftConstraints(root):
    global opt_var
    global distance_func_parts
    constr = root.find("constraint")
    if constr == None or "id" not in constr.attrib.keys() or "ProbSucc1" <> constr.attrib["id"]:
        return
    for e in constr.findall("equal"):
        if "leftNode" not in e.attrib.keys() or "rightNode" not in e.attrib.keys():
            continue
	leftNodeLabel = e.attrib["leftNode"]
        rightNodeLabel = e.attrib["rightNode"]
        if leftNodeLabel not in opt_var.keys():
            print("[ERROR]: {} is not a valid node label".format(leftNodeLabel))
        if rightNodeLabel not in opt_var.keys():
            print("[ERROR]: {} is not a valid node label".format(rightNodeLabel))
        distance_func_parts.append("({}-{})**2".format(opt_var[leftNodeLabel],opt_var[rightNodeLabel]))

    for e in constr.findall("greater"):
        if "leftNode" not in e.attrib.keys() or "rightNode" not in e.attrib.keys():
            continue
	leftNodeLabel = e.attrib["leftNode"]
        rightNodeLabel = e.attrib["rightNode"]
        if leftNodeLabel not in opt_var.keys():
            print("[ERROR]: {} is not a valid node label".format(leftNodeLabel))
        if rightNodeLabel not in opt_var.keys():
            print("[ERROR]: {} is not a valid node label".format(rightNodeLabel))
        leftNode = opt_var[leftNodeLabel]
        rightNode = opt_var[rightNodeLabel]
        distance_func_parts.append("(({}-{})**2 if {} < {} else 0)".format(leftNode,rightNode,leftNode,rightNode))

def parseTree(root):
    global index
    global opt_var
    global hard_pred_str
    global distance_func_parts
    
    opt_varname = ""
    label = root.find("label")
    if label <> None:
        if label.text not in opt_var.keys():
            opt_varname = "x[{}]".format(index)
            opt_var[label.text] = opt_varname
            opt_var_inv[index] = label.text
            index += 1
        probSucc = root.find("parameter")
        if probSucc <> None and "domainId" in probSucc.attrib.keys() \
                            and "category" in probSucc.attrib.keys() \
                            and "ProbSucc1" == probSucc.attrib["domainId"] \
                            and "basic" == probSucc.attrib["category"]:
            distance_func_parts.append("({}-{})**2".format(opt_varname,probSucc.text))

    children = root.findall("node")
    if children == None or len(children) == 0:
        return opt_varname

    child_outputs = []
    for child in children:
        child_outputs.append(parseTree(child))

    # if a node has a refinement annotation
    if "refinement" in root.attrib.keys():
        if root.attrib["refinement"] == "conjunctive":
            hard_pred_str.append("{}-{}".format("*".join(child_outputs),opt_varname))
        if root.attrib["refinement"] == "disjunctive":
            hard_pred_str.append("{}-{}".format("+".join(child_outputs),opt_varname))

    return opt_varname
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
if len(sys.argv) != 2:
    print("Usage: python script.py filename.xml")
    sys.exit()
try:

    tree = ET.parse(sys.argv[1])
    root = tree.getroot()

    parseTree(root)

    hard_predicates = {
        'type': 'eq',
        'fun': eval("lambda x : np.array([{}])".format(",".join(hard_pred_str)))
    }

    processSoftConstraints(root)

    #print("Distance function: {}".format(" + ".join(distance_func_parts)))

    #for k,v in opt_var.items():
    #    print("{} {}".format(k,v))

    x0=np.array([.5]*len(opt_var))
    bounds = [(0, 1)]*len(opt_var)

    func = eval("lambda x : {}".format(" + ".join(distance_func_parts)))

    ret = minimize(func, x0, method='SLSQP', jac="2-point", constraints=[hard_predicates], bounds=bounds, options={'ftol': 1e-9,'disp': False})
    #print("Algorithm: Sequential Least Squares Programming (SLSQP) {}".format(ret))

    printOut(ret.x)

except IOError as e:
    print 'I/O error({}): {}'.format(e.errno, e.strerror)
    sys.exit()
except:
    print 'Unexpected error:', sys.exc_info()[0]
    sys.exit()

