# at-decorator
_Attack tree decoration implementation_

This repository contains a CSP-based implemenation for the attack tree decoration problem.

The code expects a partially decorated attack tree in the ADTool XML schema format. You can create it using the ADTool <a>https://github.com/tahti/ADTool2</a>.

The code utilizes the Z3 Theorem Prover from Microsoft as a dependency. It can be obtained from <a>https://github.com/Z3Prover/z3</a>. Please follow the instructions there to install Z3py.

This repository also includes a sample attack tree and a sample input file for the solver.

## To run the CSP-based tool

1. Configure the code in [CSP_decorator/at_decorator_csp.py](./CSP_decorator/at_decorator_csp.py) to use the right file names.
2. Run the code.
3. The code will generate a Python file with a set of Z3 variables and constraints defined.
4. Add/remove desired constraints using the Z3 notation (template provided in the generated file).
5. Edit the dictionary dict that contains a mapping from Z3 soft predicate names to the soft constraints. 
6. Run the resulting Python file to obtain a solution from the Z3 prover.

## To inspect the ATM case study solution
1. Inspect the code in [Z3-example-input/z3inputfile-ATM.py](./Z3-example-input/z3inputfile-ATM.py). It has been already populated with all soft constraints defined in the article. The ATM attack tree is in [attack-trees/physical-attack-ATM-with-attributes.xml](./attack-trees/physical-attack-ATM-with-attributes.xml)
2. Run the code with the Z3 solver to see the solution.
