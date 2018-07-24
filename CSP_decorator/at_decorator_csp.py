
# coding: utf-8

# # This is a file that parses an attack tree (with some values)
# # We use Z3 to solve a constraint satisfaction problem on the parsed tree


import xml.etree.ElementTree as ET
#from z3 import *
import os
#from sets import Set


# ### CONFIG

atree = ET.parse('physical-attack-ATM-with-attributes.xml')
#domain = 'MinTime'
domain = 'Probability'

z3output = 'z3inputfile-ATM.py'
xmloutput = 'output-ATM.xml'


# #### getting domain info, but it is not currently used 


# getting the attribute domain name
root = atree.getroot()
for child in root:
    if (child.tag == 'domain'):
        attribute = child.attrib
        domain_name = attribute['id']
        print domain_name


# ### Function to add unique variables to all nodes in the tree

def variable_adder(atree):
    tree = atree
    variable_num = 0
    root = atree.getroot()
    for node in root.iter('node'):
        node.set('var_num',"v"+str(variable_num))
        variable_num = variable_num + 1
    return (tree)

# creating an auxiliary xml file that will be processed further
tree = variable_adder(atree)
tree.write(xmloutput)


# ### functions to test membership in lists 


def is_same_list(list1,list2):
    result = True
    for element in list1:
        if (element not in list2):
            result = False
    for element in list2:
        if (element not in list1):
            result = False
    return result

def is_element(list1,list2):
    result = False
    for element in list2:
        if (is_same_list(list1, element)):
            result = True
    return result


# ### defining domain operators


# return a string of format v0==v1+v2+..
def summa(top,elements):
    prepared_str = ''
    for elem in elements:
        prepared_str = prepared_str + '+' + elem
    prepared_str = prepared_str[1:]
    return top + "==" + prepared_str


# return a string of format v0<=v1,vo<=v2,... ,Or(v0==v1, v0==v2,..)
def mininum(top, elements):
    prepared_str = ''
    prepared_str1 = ''
    for elem in elements:
        prepared_str = prepared_str + top + "<=" + elem + ","
        prepared_str1 = prepared_str1 + top + "==" + elem + ","
    prepared_str = prepared_str[:-1]
    prepared_str1 = prepared_str1[:-1]     
    return prepared_str + ", " + "Or(" + prepared_str1 + ")"

# return a string of format v0>=v1, v0>=v2,..., Or(v0==v1, v0==v2,..)
def maximum(top, elements):
    prepared_str = ''
    prepared_str1 = ''
    for elem in elements:
        prepared_str = prepared_str + top + ">=" + elem + ","
        prepared_str1 = prepared_str1 + top + "==" + elem + ","
    prepared_str = prepared_str[:-1]
    prepared_str1 = prepared_str1[:-1]     
    return prepared_str + ", " + "Or(" + prepared_str1 + ")"


# return a string v0==v1*v2*..
def multiplication(top, elements):
    prepared_str = ''
    for elem in elements:
        prepared_str = prepared_str + '*' + elem
    prepared_str = prepared_str[1:]
    return top + "==" + prepared_str


# ### config for domain operators

# return a string v0==v1+v2+..-v1*v2-..+v1*v2*v3+.. - v1*v2*v3*v4*..*vn
def probability_OR(top, elements):
    prepared_str = ''
    num_children = len(elements)
    sign = True
    collection = []
    #s = set(elements)
    s = []
    s1 = []
    for elem in elements:
        s = [elem]
        s1.append(s)
        
    collection.append(s1)
    s = elements
    
    for i in range(1,num_children):
        # i is counter for number of tuples (from 1 to k)
        # form list and add it to collection
        # first list is formed
        new_list = []
        new_collection = []
        
        for elem in collection[i-1]:
            for candidate in s:
                new_list = []
                if (candidate not in elem):
                    new_list = elem[:]
                    new_list.append(candidate)
                    if (not is_element(new_list, new_collection)):
                        new_collection.append(new_list)
        collection.append(new_collection)
        new_collection = []
                        
    # got a list of sets of sets
    for elem in collection:
        prepared_str1 = ''
        for variables in elem:
            prepared_str2 = ''
            for items in variables:
                prepared_str2 = prepared_str2 + "*" + items
            prepared_str2 = prepared_str2[1:]
            
            prepared_str1 = prepared_str1 + "+" + prepared_str2
        prepared_str1 = prepared_str1[1:]
        prepared_str1 = "(" + prepared_str1 + ")"
        if sign:
            prepared_str = prepared_str + "+" + prepared_str1
        else:
            prepared_str = prepared_str + "-" + prepared_str1
        sign = not sign
    prepared_str = prepared_str[1:]            
    return top + "==" + prepared_str

def domain_op_AND(parent, children):
    if (domain == 'MinTime'):
        return maximum(parent, children)
    else:
        if (domain == 'Probability'):
            return multiplication(parent, children)
        else:
            print("ERROR! Unsupported domain name: %s\n", domain)
            return ''

def domain_op_OR(parent, children):
    if (domain == 'MinTime'):
        return minimum(parent, children)
    else:
        if (domain == 'Probability'):
            return probability_OR(parent, children)
        else:
            print("ERROR! Unsupported domain name: %s\n", domain)
            return ''

def domain_op_SAND(parent, children):
    if (domain == 'MinTime'):
        return summa(parent, children)
    else:
        if (domain == 'Probability'):
            return multiplication(parent, children)
        else:
            print("ERROR! Unsupported domain name: %s\n", domain)
            return ''


# ### various operations on attack tree xml files

def get_label(node):
    # gets label value from the node
    #label = node.find('label').text
    
    # gets var_num from the node
    label = node.get('var_num')
    return label



def is_leaf(node):
    # checks if it's a leaf node 
    element = node.find('node')
    # maybe if (not element) 
    if (element is None):
        return True
    else:
        return False



def children(node):
    # returns children nodes
    child = []
    for element in node.findall('node'):
        child.append(element)
    return child



def get_child_value(node):
    # assuming it's a leaf node
    # assuming only one domain defined in the tree
    value = node.find('parameter').text
    return value


def get_tree_var_key(atree):
    # get a mapping label <-> var_num for the tree
    tree = atree
    root = tree.getroot()
    mapping = []
    for node in root.iter('node'):
        new_elem = []
        label = node.find('label').text
        var_num = node.get('var_num')
        new_elem.append(label)
        new_elem.append(var_num)
        mapping.append(new_elem)
    return mapping


def get_tree_var_nums(atree):
    # get a set of variables for the tree (var_nums)
    tree = atree
    root = tree.getroot()
    var_nums = []
    for node in root.iter('node'):
        var_num = node.get('var_num')
        var_nums.append(var_num)
    return var_nums


# ### process an attack tree to extract tree-shape induced constraints;
# ### assume domain operations set in this code file


atree = ET.parse(xmloutput)
tree_constraints = []
defined_leaves = []
# key is node label
# value is a list with first operator name and then all children labels as a list
candidates = []
root = atree.getroot()
root_node = root.find('node')
candidates.append(root_node)

while (candidates != []):
    # get current candidate 
    node = candidates.pop()
    to_add = []
    # create an entry to describe equation
 
    if (not is_leaf(node)):
        # collect tree structure equations
        childs = children(node)
        node_key = get_label(node)
        child_list_label = []
        for elem in childs:
            child_list_label.append(get_label(elem))
        refinement = node.get('refinement')
        to_add.append(node_key)
        to_add.append(refinement)
        to_add.append(child_list_label)
        tree_constraints.append(to_add)
        # add children to the candidates list
        candidates.extend(childs)
    else:
        # collect values defined on leaf nodes
        to_add.append(get_label(node))
        to_add.append(get_child_value(node))
        defined_leaves.append(to_add)

print 'tree_constraints:'
for element in tree_constraints:
    print element
print 'leaf node values set:'
for element in defined_leaves:
    print element
    

mapping = get_tree_var_key(atree)
for element in mapping:
    print element
#var_nums = get_tree_var_nums(atree)
#for element in var_nums:
#    print element


# ## preparing a file as input for z3

var_nums = get_tree_var_nums(atree)
file = open(z3output,"w") 

file.write("from z3 import *\n")
file.write("\n")

# z3 template: 
# def f(x):
#    return If(x > 0, 1, 0)

# z3 template:
# x = Real('x')
 
for element in var_nums:
    # add element + ' = Real(' + \' + element + ')' 
    file.write(element + "= Real(" + "'" + element + "'" +")"+"\n")
    
# z3 template:
# s = Solver()

file.write('\n')
file.write('s = Solver()\n')
file.write("\n")
    
#file.close() 

# z3 template:
# s.add(v0 = v1 + v2 + v3)
# s.add(v0 = min(v1,v2)) MIN will not work; replace with a workaround

for element in tree_constraints:
    top = element[0]
    operator = element[1]
    equation = ''
    if (operator == 'conjunctive'):
        # AND = sum; 
        equation = domain_op_AND(top,element[2])
        file.write("s.add(" + equation + ")" + "\n")
    else:
        if (operator == 'disjunctive'):
            # OR = min
            equation = domain_op_OR(top,element[2])
            file.write("s.add(" + equation + ")" + "\n")
        else:
            if (operator == 'sequential'):
                # SAND = sum
                equation = domain_op_SAND(top,element[2])
                file.write("s.add(" + equation + ")" + "\n")
            else:
                file.write("ERROR! Unexpected domain operator: %s\n", operator)
                print("ERROR! Unexpected domain operator: %s\n", operator) 

file.write('\n')
            
for element in defined_leaves:
    var_num = element[0]
    value = element[1]
    equation = var_num + "==" + value
    file.write("s.add(" + equation + ")" + "\n")

file.write("\n")
file.write("# add your constraints here\n")
file.write("\n")

# z3 template:
# print s.check()
# m = s.model()
# print "x = %s" % m[x]
# 
#print "traversing model..."
#for d in m.decls():
#    print "%s = %s" % (d.name(), m[d])
    
file.write("print s.check()\n")
file.write("m = s.model()\n")
file.write("for d in m.decls():\n")
file.write('    print "%s = %s" % (d.name(), m[d]) \n')

file.close()





