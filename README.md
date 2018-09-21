# at-decorator
_Attack tree decoration implementation_

This repository contains a CSP-based and an SQP-based implemenations for the attack tree decoration problem.

The code expects a partially decorated attack tree in the ADTool XML schema format. You can create it using the ADTool <a>https://github.com/tahti/ADTool2</a>.

## CSP-based tool
The code utilizes the Z3 Theorem Prover from Microsoft as a dependency. It can be obtained from <a>https://github.com/Z3Prover/z3</a>. Please follow the instructions there to install Z3py.

This repository also includes a sample attack tree and a sample input file for the solver.

### To run it
1. Configure the code in [CSP_decorator/at_decorator_csp.py](./CSP_decorator/at_decorator_csp.py) to use the right file names.
2. Run the code.
3. The code will generate a Python file with a set of Z3 variables and constraints defined.
4. Add/remove desired constraints using the Z3 notation (template provided in the generated file).
5. Edit the dictionary dict that contains a mapping from Z3 soft predicate names to the soft constraints. 
6. Run the resulting Python file to obtain a solution from the Z3 prover.

### To inspect the ATM case study solution
1. Inspect the code in [Z3-example-input/z3inputfile-ATM.py](./Z3-example-input/z3inputfile-ATM.py). It has been already populated with all soft constraints defined in the article. The ATM attack tree is in [attack-trees/physical-attack-ATM-with-attributes.xml](./attack-trees/physical-attack-ATM-with-attributes.xml)
2. Run the code with the Z3 solver to see the solution.

## SQP-based tool
The code utilizes the scipy and numpy Python libraries. We also provide an example of an attack tree file (the ATM fraud scenario) and an example output attack tree with decorated values.  

### To run it
1. Check configuration of the file in [SQP_decorator/sqp_decorator.py](/SQP_decorator/sqp_decorator.py) to use the right files. 
2. Run the code.
3. Inspect the output tree for result.
