// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.NC.SpecialCounters {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Crypto.Basics;


    ////////////////////////////////////////////////////////////////////////////////////////////
    ///////                                                                             ////////
    ///////                          SPECIAL COUNTERS                                   ////////
    ///////                                                                             ////////
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// # Summary
    /// Returns a Counter type that references an input
    /// array of qubits, and includes operations
    /// that use shift registers for incrementing
    ///
    /// # Inputs
    /// ## counter
    /// Qubit register that will contain the counter.
    ///
    /// Output
    /// ## Counter
    /// Tuple referencing the qubits in `counter`, 
    /// as well as operations for counting based on 
    /// shift-registers
    function QubitsAsSpecialCounter (register : Qubit[]) : Counter {
        let nQubits = Length(register);
        let prepare = ConcatenateOperations(PrepareSpecialCounter, NoOp<Unit>, register, _);
        let incrementInternal = ConcatenateOperations(IncrementSpecialCounter, NoOp<Unit>, register, _);
        let test = TestSpecialCounter(register, _);
        let primitivepoly=_PrimitiveGF2Polynomial(nQubits);
        return Counter(register, 2^nQubits, prepare, incrementInternal, test);
    }


    /// # Summary
    /// Sets a SpecialCounter to its "zero" state.
    ///
    /// # Inputs
    /// ## counter
    /// A qubit register assumed to be in an all-zero state,
    /// assumed to be referenced by a Counter type.
    operation PrepareSpecialCounter(counter : Qubit[]) : Unit {
        body(...){
            ApplyToEachWrapperCA(X, counter);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Tests if a special counter is in its non-zero state; if it is, 
    /// it flips the target qubit
    ///
    /// # Inputs
    /// ## counter
    /// Qubit register  to test
    /// ## target
    /// A qubit whose state will be flipped (an X gate) if
    /// `counter` is not in its zero state.
    operation TestSpecialCounter(counter : Qubit[], target : Qubit) : Unit {
        body (...) {
            (Controlled TestSpecialCounter)(new Qubit[0], (counter, target));
        }
        controlled(controls, ...){
            (Controlled CheckIfAllOnes)(controls, (counter, target));
            (Controlled X)(controls, (target));
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Returns an irreducible polynomial over GF2 of the specified degree.
    /// Used for special counters.
    /// 
    /// # Inputs
    /// ## degree
    /// The degree of the polynomial to be returned
    ///
    /// # Outputs
    /// ## Int[]
    /// An array of coefficients in the polynomial which are non-zero, 
    /// where 0 is the constant term, 1 is x, 2 is x^2, etc.
    /// The constant term and largest term are assumed to be 1
    /// and thus omitted
    function _PrimitiveGF2Polynomial(degree : Int) : Int[]{
        let PRIMITIVE_TABLE_GF2 = [
              [ 1 ], [ 1 ], [ 1 ], [ 2 ], [ 1 ], [ 1 ], [ 2, 3, 4 ], [ 4 ], [ 3 ], [ 2 ], [ 1, 3, 5, 6, 7 ], [ 1, 3, 4 ], [ 3, 5, 7 ], [ 1 ], [ 2, 3, 5 ], [ 3 ], [ 1, 10, 12 ], 
              [ 1, 2, 5 ], [ 3 ], [ 2 ], [ 1 ], [ 5 ], [ 1, 3, 4 ], [ 3 ], [ 1, 4, 6, 7, 8, 10, 14 ], [ 1, 2, 5 ], [ 2, 5, 6, 7, 13 ], [ 2 ], [ 1, 2, 3, 5, 7, 11, 13, 16, 17 ], 
              [ 3 ], [ 3, 4, 7, 9, 15 ], [ 3, 6, 8, 10, 11, 12, 13 ], [ 1, 2, 4, 5, 6, 7, 8, 11, 12, 15, 16 ], [ 2 ], [ 1, 5, 6, 8, 13, 14, 17, 19, 20, 22, 23 ], [ 1, 4, 6 ], 
              [ 1, 5, 6 ], [ 4 ], [ 3, 4, 5 ], [ 3 ], [ 1, 2, 5, 6, 9, 11, 12, 18, 20, 24, 25, 26, 30 ], [ 3, 4, 6 ], [ 1, 3, 4, 16, 17, 19, 24 ], [ 1, 3, 4 ], [ 14, 17, 20, 21, 23 ], 
              [ 5 ], [ 3, 7, 8, 10, 11, 12, 17, 23, 25 ], [ 9 ], [ 2, 3, 4 ], [ 1, 3, 6 ], [ 3 ], [ 1, 2, 6 ], [ 1, 2, 4, 7, 13, 15, 16, 17, 18, 21, 25, 27, 29, 30, 31, 32, 34 ], 
              [ 4, 7, 9, 10, 11 ], [ 2, 4, 7 ], [ 1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 16, 19, 21 ], [ 19 ], [ 2, 4, 7 ], [ 1 ], [ 1, 2, 5 ], 
              [ 1, 6, 12, 13, 14, 16, 17, 18, 19, 20, 21, 24, 25, 26, 27, 28, 29, 30, 32  ], [ 1 ], [ 1, 3, 4 ], [ 18 ], [ 2, 4, 5, 6, 7, 11, 13, 16, 19, 21, 22, 23, 24, 27, 29, 30, 31, 32, 33, 34, 38, 40, 42, 45, 46 ], 
              [ 1, 2, 5 ], [ 9 ], [ 2, 5, 6 ], [ 1, 3, 5 ], [ 6 ], [ 3, 9, 10 ], [ 25 ], [ 3, 8, 11, 12, 13, 16, 17, 21, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,  36, 37 ], [ 1, 3, 6 ], 
              [ 1, 2, 5, 14, 15, 19, 20, 23, 24, 25, 27, 29, 31, 33, 34, 35, 36, 37, 38 ], [ 2, 5, 6 ], [ 1, 4, 6, 7, 8, 9, 11, 13, 14, 15, 17, 18, 19, 21, 22, 24, 25, 27, 28, 32,  33, 34, 35, 37, 39, 42, 43, 44, 46 ], 
              [ 9 ], [ 2, 4, 9 ], [ 4 ], [ 1, 2, 3, 4, 6, 7, 9, 11, 12, 13, 15, 16, 17, 21, 22, 24, 28, 32, 33, 34,  35, 36, 37 ], [ 2, 4, 7 ], [ 2, 4, 5, 7, 8, 9, 11, 12, 13, 16, 17, 20, 21, 24, 25, 26, 28, 31, 32, 37,  39, 41, 46, 47, 48, 52, 57 ], 
              [ 1, 2, 8 ], [ 1, 2, 5, 6, 7, 8, 9, 10, 12, 14, 16, 21, 22, 25, 27, 31, 38, 40, 43 ], [ 13 ], [ 1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 18, 19, 21, 24, 27, 28, 30, 31,  33, 36, 38, 41, 44, 45, 47 ], [ 38 ], [ 2, 4, 7, 10, 11, 12, 14, 16, 18, 24, 25, 26, 28, 30, 32, 34, 36, 37, 38,  39, 40, 42, 44, 45, 46, 47, 48, 50, 51, 53, 55, 56, 57, 58, 60, 61, 62, 63,  64 ], [ 1, 5, 8 ], [ 2, 4, 5, 9, 12, 14, 15, 16, 17, 18, 21, 22, 23, 24, 30, 32, 33, 37, 38,  40, 41, 42, 43, 44, 48 ], [ 2 ], [ 21 ], [ 11 ], [ 6, 9, 10 ], [ 6 ], [ 11 ], [ 1, 2, 4, 6, 32, 33, 34, 35, 64, 65, 66, 67, 96, 97, 98 ], 
              [ 3, 5, 6, 8, 9, 11, 15, 16, 19, 20, 22, 24, 25, 27, 30, 31, 34, 35, 36, 37, 41, 43, 44, 45, 46, 47, 48, 52, 55, 56, 57 ]
        ];
        Fact(degree < Length(PRIMITIVE_TABLE_GF2) + 2, $"Degree {degree} is too large for table (max degree {Length(PRIMITIVE_TABLE_GF2) + 1}");
        return PRIMITIVE_TABLE_GF2[degree - 2];
    }

    /// # Summary
    /// Increments a special counter by 1.
    ///
    /// # Inputs
    /// ## counter
    /// Qubit register of the counter to increment.
    operation IncrementSpecialCounter(counter : Qubit[]) : Unit {
        body (...) {
            (Controlled IncrementSpecialCounter)(new Qubit[0], (counter));
        }
        controlled (controls, ...){
            let nQubits=Length(counter);
            (Controlled CyclicRotateRegister)(controls, LittleEndian(counter));
            let polynomial = _PrimitiveGF2Polynomial(nQubits);
            for (idp in 0..Length(polynomial) - 1){
                (Controlled CNOT)(controls, (counter[0], counter[polynomial[idp]]));
            }
        }
        controlled adjoint auto;
    }

   


    
}