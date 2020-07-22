# Summary

All of the tests follow the same basic format. There are three main functions:

# [OperationName]TestHelper

This is the function which actually calls the operation being tested. It does the following
steps:

1. Allocate qubits and format variables to correctly point to the qubit registers.
2. Write the classical test case to the qubit registers.
3. Perform the operation being tested.
4. Classicaly compute the expected result.
5. Measure the qubit registers. Here we assume that measuring a register
resets the state of the register to 0.
6. Compare the measured results to the expected results, and throw an error if they do not match. This also 
includes comparing the measured inputs to the original inputs, which should remain unchanged. 
7. Initialize one control qubit to 0.
8. Run steps 2-6, but control the operation. Here, there should be no change to inputs or outputs.
9. Flip the control qubit to 1.
10. Run steps 2-6, but contol the operation. 
11. Initialize another control qubit, and set both to 0.
12. Run steps 8-10 with 2 control qubits instead of 1.

## Inputs

### Operation : ('T => Unit is Ctl)

This is the operation being tested. It takes some inputs (here 'T) and performs quantum
operations on them.

### Classical inputs

Here the function takes some classical inputs (such as `Int`, `BigInt`, etc.). These
are XORed into the qubit register for the test. 

### nQubits

The number of qubits to parameterize the operation. For example: An addition with 
`nQubits=10` will add 10-bit integers, and thus need 20 qubits in total (21 if it uses
a carry).

## Open Operations

Some operations are "open", meaning they do not clean up their ancilla. An `TestHelper`
for an open function also needs a `nAncilla` argument, telling it how many ancilla to 
allocate. The operation also needs an adjoint.

The steps for the open version are slightly different:

1. Allocate qubits and format variables to correctly point to the qubit registers.
2. Write the classical test case to the qubit registers.
3. Perform the operation being tested.
4. Classicaly compute the expected result.
5. Measure the input and output qubit registers, but not the ancilla
6. Compare the measured results to the expected results, and throw an error if they do not match. This also 
includes comparing the measured inputs to the original inputs, which should remain unchanged. 
7. Rewrite the measurement results to the corresponding registers.
8. Perform the *adjoint* of the operation being tested.
9. Measure all registers, and check that (a) the inputs are in their original state and (b) the output
and ancilla are 0.
10. Initialize one control qubit to 0.
11. Run steps 2-9, but control the operation. Here, there should be no change to inputs or outputs.
12. Flip the control qubit to 1.
13. Run steps 2-9, but contol the operation. 
11. Initialize another control qubit, and set both to 0.
12. Run steps 10-13 with 2 control qubits instead of 1.

# [OperationName]Test

Takes a specific test case and calls `[OperationName]TestHelper` directly
with this test case.

# [OperationName]ExhaustiveTestHelper

Takes an operation and a number of qubits, and runs `[Operationname]TestHelper`
with that number of qubits for every possible input. 

For certain operations, this operation does a lot of preprocessing to ensure the inputs
are well-formatted. For example, modular multiplication presently only functions
correctly with odd moduli. 

# [OperationName]ExhaustiveTest

Contains a hard-coded number of qubits (and ancilla, for open operations) and calls
`[OperationName]ExhaustiveTestHelper` with those qubits, as well as a specific function.

If there are multiple variants of the same operation (for example: different RipplyCarry 
adders, or a carry lookahead adder), they will all use the same `TestHelper` but they
will have distinct `[OperationName]ExhaustiveTest` operations. 

# [OperationName][TestType]Reversible

Operations like this are exactly the same as the other versions, but they are expected to 
use numbers of qubits that are beyond what the fully quantum simulator can reasonably simulate.

# [OperationName]RandomTestHelper

For certain operations and certain parameters, an exhaustive test is not feasible. Thus, we use
a random test. These operations will select random parameters, and pass them to `[OperationName]TestHelper`.

These operations also require a `nTests` input, which tells it how many tests to run. 


