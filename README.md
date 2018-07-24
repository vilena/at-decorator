# at-decorator
Attack tree decoration implementation

This repository contains a CSP-based implemenation for the attack tree decoration problem.

The code expects a partially decorated attack tree in the ADTool XML schema format. You can create it using the ADTool <a>https://github.com/tahti/ADTool2</a>.

The code utilizes the Z3 Theorem Prover from Microsoft as a dependency. It can be obtained from <a>https://github.com/Z3Prover/z3</a>.

The repository also includes a sample attack tree.

## To run the Z3-based tool

1. Configure the code in CSP_decorator/at_decorator_csp.py 
2. Run the code
3. The code will generate a python file with a set of Z3 variables defined
4. Add/remove desired constraints
5. Run the resulting python file to obtain a solution from the Z3 prover

