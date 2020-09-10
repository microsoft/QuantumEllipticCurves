// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Tests {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;

    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.ModularArithmetic;

    open Microsoft.Quantum.ModularArithmetic.DebugHelpers;
    
    ///////////////// MODULAR ADDITION /////////////////
    ///
    /// # Summary
    /// Reversible, in-place modular addition of two integers modulo a third. 
    /// Given two $n$-bit integers x and y encoded in LittleEndian registers 
    /// `xs` and `ys`, and an integer modulus m encoded in the LittleEndian  
    /// register `ms`, the operation computes the sum x + y mod m. 
    /// The result is held in the register `ys`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the first integer summand, remains 
    /// unchanged.
    /// ## ys
    /// Qubit register encoding the second integer summand, is 
    /// replaced with the sum modulo m.
    /// ## ms
    /// Qubit register encoding the integer modulus.
    /// 
    /// # Operations
    /// This can test:
    ///		* ModularAdd
     operation ModularAddTestHelper(
        Adder : ((LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), 
        summand1 : BigInt, 
        summand2 : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
     ) : Unit {
        using (register = Qubit[3 * nQubits]) {
            // Bookkeeping and ancilla allocation
            mutable actual1 = 0L;
            mutable actual2 = 0L;
            mutable actualm = 0L;
            let summand1LE = LittleEndian(register[0 .. nQubits - 1]);
            let summand2LE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
            let modulusLE = LittleEndian(register[2 * nQubits .. 3 * nQubits - 1]);
 
            // Write to qubit registers
            ApplyXorInPlaceL(summand1, summand1LE);
            ApplyXorInPlaceL(summand2, summand2LE);
            ApplyXorInPlaceL(modulus, modulusLE);

            // Run test
            Adder(summand1LE, summand2LE, modulusLE);
 
            // Compute expected classical result
            let expected = (summand1 + summand2) % modulus;

            // Check results
            set actual1 = MeasureBigInteger(summand1LE);
            Fact(summand1== actual1, $"Input: Expected {summand1}, got {actual1}");
            set actual2 = MeasureBigInteger(summand2LE);
            Fact(expected== actual2, $"Expected {expected}, got {actual2}");
            set actualm = MeasureBigInteger(modulusLE);
            Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    ApplyXorInPlaceL(summand1, summand1LE);
                    ApplyXorInPlaceL(summand2, summand2LE);
                    ApplyXorInPlaceL(modulus, modulusLE);

                    // controls are |0>, no addition is computed
                    // Run test
                    (Controlled Adder) (controls, (summand1LE, summand2LE, modulusLE));

                    // Check results
                    set actual1 = MeasureBigInteger(summand1LE);
                    Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
                    set actual2 = MeasureBigInteger(summand2LE);
                    Fact(summand2== actual2, $"Expected {summand2}, got {actual2}");
                    set actualm = MeasureBigInteger(modulusLE);
                    Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

                    // Write to qubit registers
                    ApplyXorInPlaceL(summand1, summand1LE);
                    ApplyXorInPlaceL(summand2, summand2LE);
                    ApplyXorInPlaceL(modulus, modulusLE);

                    // Flip controls 
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Adder) (controls, (summand1LE, summand2LE, modulusLE));

                    // Check results
                    set actual1 = MeasureBigInteger(summand1LE);
                    Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
                    set actual2 = MeasureBigInteger(summand2LE);
                    Fact(expected== actual2, $"Expected {expected}, got {actual2}");
                    set actualm = MeasureBigInteger(modulusLE);
                    Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation ModularAddExhaustiveTestHelper (Adder : ((LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int) : Unit {
        for( modulus in 2^(nQubits-1) .. 2^nQubits - 1 ) {
            for( summand1 in 0 .. modulus - 1 ) {
                for( summand2 in 0 .. modulus - 1 ) {
                    ModularAddTestHelper(Adder, IntAsBigInt(summand1), IntAsBigInt(summand2), IntAsBigInt(modulus), nQubits);
                }
            }
        }
    }

    operation ModularAddTest () : Unit {
        let nQubits = 7;
        let modulus = 127L;
        let summand1 = 111L; 
        let summand2 = 90L; 
        ModularAddTestHelper(ModularAdd, summand1, summand2, modulus, nQubits);
    }

    operation ModularAddExhaustiveTest () : Unit {
        let nQubits = 3;
        ModularAddExhaustiveTestHelper (ModularAdd, nQubits);
    }

    operation ModularAddTestReversible () : Unit {
        let nQubits = 17;
        let modulus = 131071L;
        let summand1 = 31579L; 
        let summand2 = 81785L;  
        ModularAddTestHelper(ModularAdd, summand1, summand2, modulus, nQubits);
    }

    operation ModularAddExhaustiveTestReversible () : Unit {
        let nQubits = 5;
        ModularAddExhaustiveTestHelper (ModularAdd, nQubits);
    }

    ///////////////// MODULAR NEGATION /////////////////
    ///
    /// # Summary
    /// Reversible, in-place modular negation of an integer modulo another 
    /// integer. Given an n-bit integer x encoded in a LittleEndian register 
    /// `xs` and an integer modulus m encoded in the LittleEndian  
    /// register `ms`, the operation computes the negative -x \mod m = m -x. 
    /// The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer, is replaced with 
    /// the negative modulo m.
    /// ## ms
    /// Qubit register encoding the integer modulus.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularNeg
   operation ModularNegTestHelper(
        Negater : ((LittleEndian, LittleEndian) => Unit is Ctl), 
        integer : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        using (register = Qubit[2 * nQubits]) {
            // Bookkeeping and qubit allocation
            mutable actual1 = 0L;
            mutable actualm = 0L;
            let integerLE = LittleEndian(register[0 .. nQubits - 1]);
            let modulusLE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
        
            // Write to qubit registers
            ApplyXorInPlaceL(integer, integerLE);
            ApplyXorInPlaceL(modulus, modulusLE);

            // Run test
            Negater(integerLE, modulusLE);
 
            // Compute expected classical result
            let expected = (modulus - integer) % modulus;

            // Check results
            set actual1 = MeasureBigInteger(integerLE);
            Fact(expected== actual1, $"Expected {expected}, got {actual1}");
            set actualm = MeasureBigInteger(modulusLE);
            Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    ApplyXorInPlaceL(integer, integerLE);
                    ApplyXorInPlaceL(modulus, modulusLE);

                    // controls are |0>, no negation is computed
                    // Run test
                    (Controlled Negater) (controls, (integerLE, modulusLE));

                    // Check results
                    set actual1 = MeasureBigInteger(integerLE);
                    Fact(integer== actual1, $"Expected {integer}, got {actual1}");
                    set actualm = MeasureBigInteger(modulusLE);
                    Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

                    // Write to qubit registers
                    ApplyXorInPlaceL(integer, integerLE);
                    ApplyXorInPlaceL(modulus, modulusLE);

                    // Flip controls
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Negater) (controls, (integerLE, modulusLE));

                    // Check results
                    set actual1 = MeasureBigInteger(integerLE);
                    Fact(expected==actual1, $"Expected {expected}, got {actual1}");
                    set actualm = MeasureBigInteger(modulusLE);
                    Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation ModularNegExhaustiveTestHelper (Negater : ((LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int) : Unit {
        for(modulus in 2^(nQubits-1) .. 2^nQubits - 1 ) {
            for(integer in 0 .. modulus - 1 ) {
                ModularNegTestHelper(Negater, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits);
            }
        }
    }

    operation ModularNegTest () : Unit {
        let nQubits = 7;
        let modulus = 127L;
        let integer = 111L; 
        ModularNegTestHelper(ModularNeg, integer, modulus, nQubits);
    }

    operation ModularNegExhaustiveTest () : Unit {
        let nQubits = 3;
        ModularNegExhaustiveTestHelper (ModularNeg, nQubits);
    }

    operation ModularNegTestReversible () : Unit {
        let nQubits = 17;
        let modulus = 131071L;
        let integer = 31579L; 
        ModularNegTestHelper(ModularNeg, integer, modulus, nQubits);
    }

    operation ModularNegExhaustiveTestReversible () : Unit {
        let nQubits = 5;
        ModularNegExhaustiveTestHelper (ModularNeg, nQubits);
    }

    ///////////////// MODULAR DOUBLING /////////////////
    ///
    /// # Summary
    /// Reversible, in-place modular doubling of an integer modulo another 
    /// integer. Given an n-bit integer x encoded in a LittleEndian register 
    /// `xs` and an integer modulus m encoded in the LittleEndian  
    /// register `ms`, the operation computes the double 2*x = x + x \mod m. 
    /// The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer, is replaced with 
    /// 2x \mod m.
    /// ## ms
    /// Qubit register encoding the integer modulus.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularDbl
    operation ModularDblTestHelper(
        Doubler : ((LittleEndian, LittleEndian) => Unit is Ctl), 
        integer : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        using (register = Qubit[2 * nQubits]) {
            // Bookkeeping and ancilla allocation
            mutable actual1 = 0L;
            mutable actualm = 0L;
            let integerLE = LittleEndian(register[0 .. nQubits - 1]);
            let modulusLE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
 
            // Write to qubit registers
            ApplyXorInPlaceL(integer, integerLE);
            ApplyXorInPlaceL(modulus, modulusLE);

            // Run test
            Doubler(integerLE, modulusLE);
 
            // Compute expected classical result
            let expected = (2L * integer)% modulus;

            // Check results
            set actual1 = MeasureBigInteger(integerLE);
            Fact(expected== actual1, $"Expected {expected}, got {actual1}");
            set actualm = MeasureBigInteger(modulusLE);
            Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    ApplyXorInPlaceL(integer, integerLE);
                    ApplyXorInPlaceL(modulus, modulusLE);

                    // controls are |0>, no negation is computed
                    // Run test
                    (Controlled Doubler) (controls, (integerLE, modulusLE));

                    // Check results
                    set actual1 = MeasureBigInteger(integerLE);
                    Fact(integer== actual1, $"Expected {integer}, got {actual1}");
                    set actualm = MeasureBigInteger(modulusLE);
                    Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

                    // Write to qubit registers
                    ApplyXorInPlaceL(integer, integerLE);
                    ApplyXorInPlaceL(modulus, modulusLE);

                    // Flip controls
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Doubler) (controls, (integerLE, modulusLE));

                    // Check results
                    set actual1 = MeasureBigInteger(integerLE);
                    Fact(expected== actual1, $"Expected {expected}, got {actual1}");
                    set actualm = MeasureBigInteger(modulusLE);
                    Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation ModularDblExhaustiveTestHelper (Doubler : ((LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int) : Unit {
        body (...) {
            for( modulus in 2^(nQubits-1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    ModularDblTestHelper(Doubler, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits);
                }
            }
        }
    }

    operation ModularDblTest () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let integer = 111L; 
            ModularDblTestHelper(ModularDbl, integer, modulus, nQubits);
        }
    }

    operation ModularDblExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularDblExhaustiveTestHelper (ModularDbl, nQubits);
        }
    }

    operation ModularDblTestReversible () : Unit {
        body (...) {
            let nQubits = 17;
            let modulus = 131071L;
            let integer = 31579L; 
            ModularDblTestHelper(ModularDbl, integer, modulus, nQubits);
        }
    }

    operation ModularDblExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 5;
            ModularDblExhaustiveTestHelper (ModularDbl, nQubits);
        }
    }

    ///////////////// MODULAR MULTIPLICATION /////////////////
    ///
    /// # Summary
    /// Reversible, out-of-place modular multiplication of two integers modulo 
    /// another integer. Given two n-bit integers x and y encoded in LittleEndian 
    /// registers `xs` and `ys`, and an integer modulus m encoded in the LittleEndian 
    /// register `ms`, the operation computes the product x*y mod m. 
    /// The result is held in the third register `zs`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y.
    /// ## zs
    /// Qubit register for the result. Must be in
    /// state 0 initially.
    /// ## ms
    /// Qubit register encoding the integer modulus.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularMulDblAdd
    operation ModularMultiplierTestHelper( 
        ModularMultiplier : ( (LittleEndian, LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), 
        multiplier1 : BigInt, 
        multiplier2 : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            //Bookkeeping and qubit allocation
            using (register = Qubit[4 * nQubits]) {
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                mutable actualr = 0L;
                mutable actualm = 0L;
                let multiplier1LE = LittleEndian(register[0 .. nQubits - 1]);
                let multiplier2LE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
                let resultLE = LittleEndian(register[2 * nQubits .. 3 * nQubits - 1]);
                let modulusLE = LittleEndian(register[3 * nQubits .. 4 * nQubits - 1]); 
 
                // Write to qubit registers
                ApplyXorInPlaceL(multiplier1, multiplier1LE);
                ApplyXorInPlaceL(multiplier2, multiplier2LE);
                ApplyXorInPlaceL(0L, resultLE);
                ApplyXorInPlaceL(modulus, modulusLE);

                // Run test
                ModularMultiplier(multiplier1LE, multiplier2LE, resultLE, modulusLE);
 
                // Compute expected classical result
                let prod = multiplier1 * multiplier2;
                let expected = prod % modulus;

                // Check results
                set actual1 = MeasureBigInteger(multiplier1LE);
                Fact(multiplier1== actual1, $"Expected {multiplier1}, got {actual1}");
                set actual2 = MeasureBigInteger(multiplier2LE);
                Fact(multiplier2== actual2, $"Expected {multiplier2}, got {actual2}");                
                set actualm = MeasureBigInteger(modulusLE);
                Fact(modulus==actualm, $"Expected {modulus}, got {actualm}");
                set actualr = MeasureBigInteger(resultLE);
                Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(multiplier1, multiplier1LE);
                        ApplyXorInPlaceL(multiplier2, multiplier2LE);
                        ApplyXorInPlaceL(0L, resultLE);
                        ApplyXorInPlaceL(modulus, modulusLE);

                        // controls are |0>, no multiplication is computed
                        // Run test
                        (Controlled ModularMultiplier) (controls, (multiplier1LE, multiplier2LE, resultLE, modulusLE));

                        // Check results
                        set actual1 = MeasureBigInteger(multiplier1LE);
                        Fact(multiplier1== actual1, $"Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureBigInteger(multiplier2LE);
                        Fact(multiplier2== actual2, $"Expected {multiplier2}, got {actual2}");                
                        set actualm = MeasureBigInteger(modulusLE);
                        Fact(modulus==actualm, $"Expected {modulus}, got {actualm}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(0L== actualr, $"Expected {0}, got {actualr}");

                        // Write to qubit registers
                        ApplyXorInPlaceL(multiplier1, multiplier1LE);
                        ApplyXorInPlaceL(multiplier2, multiplier2LE);
                        ApplyXorInPlaceL(0L, resultLE);
                        ApplyXorInPlaceL(modulus, modulusLE);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularMultiplier) (controls, (multiplier1LE, multiplier2LE, resultLE, modulusLE));

                        // Check results
                        set actual1 = MeasureBigInteger(multiplier1LE);
                        Fact(multiplier1== actual1, $"Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureBigInteger(multiplier2LE);
                        Fact(multiplier2== actual2, $"Expected {multiplier2}, got {actual2}");                
                        set actualm = MeasureBigInteger(modulusLE);
                        Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

   operation ModularMultiplierExhaustiveTestHelper ( ModularMultiplier : ( (LittleEndian, LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int ) : Unit {
        body (...) {
            for( modulus in 2^(nQubits-1)+1 ..2.. 2^nQubits - 1 ) {
                for( multiplier1 in 0 .. modulus - 1 ) {
                    for( multiplier2 in 0 .. modulus - 1 ) {
                        ModularMultiplierTestHelper(ModularMultiplier, IntAsBigInt(multiplier1), IntAsBigInt(multiplier2), IntAsBigInt(modulus), nQubits);
                    }
                }
            }
        }
    }

    operation ModularMulDblAddTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let multiplier1 = 13L;
            let multiplier2 = 9L; 
            ModularMultiplierTestHelper(ModularMulDblAdd, multiplier1, multiplier2, modulus, nQubits);
        }
    }

    operation ModularMulDblAddExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularMultiplierExhaustiveTestHelper (ModularMulDblAdd, nQubits);
        }
    }

    operation ModularMulDblAddTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let multiplier1 = 13L;
            let multiplier2 = 42L; 
            ModularMultiplierTestHelper(ModularMulDblAdd, multiplier1, multiplier2, modulus, nQubits);
        }
    }

    operation ModularMulDblAddExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;
            ModularMultiplierExhaustiveTestHelper (ModularMulDblAdd, nQubits);
        }
    }

    ///////////////// MODULAR SQUARING /////////////////
    ///
    /// # Summary
    /// Reversible, out-of-place modular squaring of an integer modulo 
    /// another integer. Given an n-bit integer x encoded in a LittleEndian 
    /// register `xs` and an integer modulus m encoded in the LittleEndian 
    /// register `ms`, the operation computes the square x^2 = x*x mod m. 
    /// The result is held in the register `zs`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## zs
    /// Qubit register for the result. Must be in
    /// state 0 initially.
    /// ## ms
    /// Qubit register encoding the integer modulus.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularSquDblAdd
    operation ModularSquarerTestHelper( ModularSquarer : ( (LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), integer : BigInt, modulus : BigInt, nQubits : Int ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[3 * nQubits]) {
                mutable actual = 0L;
                mutable actualr = 0L;
                mutable actualm = 0L;
                let integerLE = LittleEndian(register[0 .. nQubits - 1]);
                let resultLE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
                let modulusLE = LittleEndian(register[2 * nQubits .. 3 * nQubits - 1]); 
 
                // Write to qubit registers
                ApplyXorInPlaceL(integer, integerLE);
                ApplyXorInPlaceL(0L, resultLE);
                ApplyXorInPlaceL(modulus, modulusLE);

                // Run test
                ModularSquarer(integerLE, resultLE, modulusLE);
 
                // Compute classical expected result
                let square = integer * integer;
                let expected = (square)%modulus;

                // Check results
                set actual = MeasureBigInteger(integerLE);
                Fact(integer==actual, $"Expected {integer}, got {actual}");
                set actualm = MeasureBigInteger(modulusLE);
                Fact(modulus==actualm, $"Expected {modulus}, got {actualm}");
                set actualr = MeasureBigInteger(resultLE);
                Fact(expected==actualr, $"Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(integer, integerLE);
                        ApplyXorInPlaceL(0L, resultLE);
                        ApplyXorInPlaceL(modulus, modulusLE);

                        // controls are |0>, no squaring is computed
                        // Run test
                        (Controlled ModularSquarer) (controls, (integerLE, resultLE, modulusLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Expected {integer}, got {actual}");
                        set actualm = MeasureBigInteger(modulusLE);
                        Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(0L== actualr, $"Expected {0}, got {actualr}");

                        // Write to qubit registers
                        ApplyXorInPlaceL(integer, integerLE);
                        ApplyXorInPlaceL(0L, resultLE);
                        ApplyXorInPlaceL(modulus, modulusLE);

                        // now controls are set to |1>, squaring is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularSquarer) (controls, (integerLE, resultLE, modulusLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Expected {integer}, got {actual}");
                        set actualm = MeasureBigInteger(modulusLE);
                        Fact(modulus== actualm, $"Expected {modulus}, got {actualm}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

   operation ModularSquarerExhaustiveTestHelper ( ModularSquarer : ( (LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    ModularSquarerTestHelper(ModularSquarer, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits);
                }
            }
        }
    }

    operation ModularSquDblAddTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            ModularSquarerTestHelper(ModularSquDblAdd, integer, modulus, nQubits);
        }
    }

    operation ModularSquDblAddExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularSquarerExhaustiveTestHelper (ModularSquDblAdd, nQubits);
        }
    }

    operation ModularSquDblAddTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let integer = 13L; 
            ModularSquarerTestHelper(ModularSquDblAdd, integer, modulus, nQubits);
        }
    }

    operation ModularSquDblAddExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;
            ModularSquarerExhaustiveTestHelper (ModularSquDblAdd, nQubits);
        }
    }

    ///////////////// MODULAR ADDITION WITH CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Reversible, in-place modular addition of two integers modulo a constant 
    /// integer modulus. Given two $n$-bit integers x and y encoded in LittleEndian  
    /// registers `xs` and `ys`, and a constant integer `modulus`, the operation computes 
    /// the sum x + y \mod modulus. The result is held in the register `ys`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularAddConstantModulus
   operation ModularAddConstantModulusTestHelper(ModularAdder : ((BigInt, LittleEndian, LittleEndian) => Unit is Ctl), summand1 : BigInt, summand2 : BigInt, modulus : BigInt, nQubits : Int ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                let summand1LE = LittleEndian(register[0 .. nQubits - 1]);
                let summand2LE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
 
                // Write to qubit registers
                ApplyXorInPlaceL(summand1, summand1LE);
                ApplyXorInPlaceL(summand2, summand2LE);

                // Run test
                ModularAdder(modulus, summand1LE, summand2LE);
 
                // Compute classical expected result
                let expected = (summand1 + summand2)%modulus;

                // Check results
                set actual1 = MeasureBigInteger(summand1LE);
                Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
                set actual2 = MeasureBigInteger(summand2LE);
                Fact(expected== actual2, $"Expected {expected}, got {actual2}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(summand1, summand1LE);
                        ApplyXorInPlaceL(summand2, summand2LE);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled ModularAdder) (controls, (modulus, summand1LE, summand2LE));

                        // Check results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
                        set actual2 = MeasureBigInteger(summand2LE);
                        Fact(summand2== actual2, $"Expected {summand2}, got {actual2}");

                        // Write to qubit registers
                        ApplyXorInPlaceL(summand1, summand1LE);
                        ApplyXorInPlaceL(summand2, summand2LE);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularAdder) (controls, (modulus, summand1LE, summand2LE));

                        // Check results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
                        set actual2 = MeasureBigInteger(summand2LE);
                        Fact(expected== actual2, $"Expected {expected}, got {actual2}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularAddConstantModulusExhaustiveTestHelper (ModularAdder : ((BigInt, LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int) : Unit {
        body (...) {
            for( modulus in 2^(nQubits-1) .. 2^nQubits - 1 ) {
                for( summand1 in 0 .. modulus - 1 ) {
                    for( summand2 in 0 .. modulus - 1 ) {
                        ModularAddConstantModulusTestHelper(ModularAdder, IntAsBigInt(summand1), IntAsBigInt(summand2), IntAsBigInt(modulus), nQubits);
                    }
                }
            }
        }
    }

    operation ModularAddConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let summand1 = 111L; 
            let summand2 = 90L; 
            ModularAddConstantModulusTestHelper(ModularAddConstantModulus, summand1, summand2, modulus, nQubits);
        }
    }

    operation ModularAddConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 4;
            ModularAddConstantModulusExhaustiveTestHelper (ModularAddConstantModulus, nQubits);
        }
    }

    operation ModularAddConstantModulusTestReversible () : Unit {
        body (...) {
            let nQubits = 11;
            let modulus = 2017L;
            let summand1 = 1579L; 
            let summand2 = 1785L;  
            ModularAddConstantModulusTestHelper(ModularAddConstantModulus, summand1, summand2, modulus, nQubits);
        }
    }

    operation ModularAddConstantModulusExhaustiveTestReversible () : Unit {
        body (...) {
            for (nQubits in 2..15) {
                ModularAddConstantModulusExhaustiveTestHelper (ModularAddConstantModulus, nQubits);
            }
        }
    }

    ///////////////// MODULAR DOUBLING WITH CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// # Input
    /// Reversible, in-place modular doubling of an integer modulo a constant 
    /// integer modulus. Given the n-bit integer x encoded in the LittleEndian  
    /// register `xs` and a constant integer `modulus`, the operation computes 
    /// the double 2x = x + x mod modulus. The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the first integer x.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularDblConstantModulus
    operation ModularDblConstantModulusTestHelper(
        Doubler : ((BigInt, LittleEndian) => Unit is Ctl), 
        integer : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual1 = 0L;
                let integerLE = LittleEndian(register[0 .. nQubits - 1]);
 
                // Write to qubit register
                ApplyXorInPlaceL(integer, integerLE);

                // Run test
                ModularDblConstantModulus(modulus, integerLE);
 
                // Compute expected classical result
                let expected = (2L * integer)%modulus;

                // Check results
                set actual1 = MeasureBigInteger(integerLE);
                Fact(expected==actual1, $"Expected {expected}, got {actual1}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);

                        // controls are |0>, no negation is computed
                        // Run test
                        (Controlled ModularDblConstantModulus) (controls, (modulus, integerLE));
                        set actual1 = MeasureBigInteger(integerLE);
                        Fact(integer==actual1, $"Expected {integer}, got {actual1}");
                        ApplyXorInPlaceL(integer, integerLE);
                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);
                        (Controlled ModularDblConstantModulus) (controls, (modulus, integerLE));
                        set actual1 = MeasureBigInteger(integerLE);
                        Fact(expected== actual1, $"Expected {expected}, got {actual1}");
                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularDblConstantModulusExhaustiveTestHelper (Doubler : ((BigInt, LittleEndian) => Unit is Ctl), nQubits : Int) : Unit {
        body (...) {
            for( modulus in 2^(nQubits-1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    ModularDblConstantModulusTestHelper(Doubler, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits);
                }
            }
        }
    }

    operation ModularDblConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let integer = 111L; 
            ModularDblConstantModulusTestHelper(ModularDblConstantModulus, integer, modulus, nQubits);
        }
    }

    operation ModularDblConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularDblConstantModulusExhaustiveTestHelper (ModularDblConstantModulus, nQubits);
        }
    }

    operation ModularDblConstantModulusTestReversible () : Unit {
        body (...) {
            let nQubits = 17;
            let modulus = 131071L;
            let integer = 31579L; 
            ModularDblConstantModulusTestHelper(ModularDblConstantModulus, integer, modulus, nQubits);
        }
    }

    operation ModularDblConstantModulusExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 5;
            ModularDblConstantModulusExhaustiveTestHelper (ModularDblConstantModulus, nQubits);
        }
    }

    ///////////////// MODULAR ADDITION BY CONSTANT WITH CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Reversible, in-place modular addition of an integer constant to an integer x
    /// encoded in a LittleEndian qubit register `xs`, modulo an integer constant `modulus`.
    /// Given the n-bit integer x encoded in the register `xs`, this operation computes
    /// x + constant mod modulus, the result is held in the register `xs`.
    ///
    /// # Input
    /// ## constant
    /// Constant integer summand.
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the first integer x.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularAddConstantConstantModulusLowT
    ///		* ModularAddConstantConstantModulusSimple
   operation ModularAddConstantConstantModulusTestHelper( Adder:((BigInt, BigInt, LittleEndian) => Unit is Ctl), summand1 : BigInt, summand2 : BigInt, modulus : BigInt, nQubits : Int ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual1 = 0L;
                let summand1LE = LittleEndian(register[0 .. nQubits - 1]);
                let summand2LE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
 
                // Writ eto qubit register
                ApplyXorInPlaceL(summand1, summand1LE);

                // Run test
                Adder(summand2, modulus, summand1LE);
            
                // Compute classical expected result
                let expected = (summand1 + summand2) % modulus;

                // Check result
                set actual1 = MeasureBigInteger(summand1LE);
                Fact(expected== actual1, $"Expected {expected}, got {actual1}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        ApplyXorInPlaceL(summand1, summand1LE);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled Adder) (controls, (summand2, modulus, summand1LE));

                        // Check results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");

                        // Write to qubit register
                        ApplyXorInPlaceL(summand1, summand1LE);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled Adder) (controls, (summand2, modulus, summand1LE));

                        // Check results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(expected==actual1, $"Expected {expected}, got {actual1}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularAddConstantConstantModulusExhaustiveTestHelper (Adder:((BigInt, BigInt, LittleEndian)=>Unit is Ctl), nQubits : Int) : Unit {
        body (...) {
            for( modulus in 2^(nQubits-1) .. 2^nQubits - 1 ) {
                for( summand1 in 0 .. modulus - 1) {
                    for( summand2 in 0 .. modulus - 1 ) {
                        ModularAddConstantConstantModulusTestHelper(Adder, IntAsBigInt(summand1), IntAsBigInt(summand2), IntAsBigInt(modulus), nQubits);
                    }
                }
            }
        }
    }

    operation ModularAddConstantConstantModulusLowTTest () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let summand1 = 111L; 
            let summand2 = 90L; 
            ModularAddConstantConstantModulusTestHelper(ModularAddConstantConstantModulusLowT, summand1, summand2, modulus, nQubits);
        }
    }

    operation ModularAddConstantConstantModulusLowTExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularAddConstantConstantModulusExhaustiveTestHelper (ModularAddConstantConstantModulusLowT, nQubits);
        }
    }

    operation ModularAddConstantConstantModulusLowTTestReversible () : Unit {
        body (...) {
            let nQubits = 11;
            let modulus = 2017L;
            let summand1 = 1579L; 
            let summand2 = 1785L;  
            ModularAddConstantConstantModulusTestHelper(ModularAddConstantConstantModulusLowT, summand1, summand2, modulus, nQubits);
        }
    }

    operation ModularAddConstantConstantModulusExhaustiveLowTTestReversible () : Unit {
        body (...) {
            let nQubits = 5;
            ModularAddConstantConstantModulusExhaustiveTestHelper (ModularAddConstantConstantModulusLowT, nQubits);
        }
    }

    operation ModularAddConstantConstantModulusSimppleTestReversible () : Unit {
        body (...) {
            let nQubits = 11;
            let modulus = 2017L;
            let summand1 = 1579L; 
            let summand2 = 1785L;  
            ModularAddConstantConstantModulusTestHelper(ModularAddConstantConstantModulusSimple, summand1, summand2, modulus, nQubits);
        }
    }

    operation ModularAddConstantConstantModulusSimpleExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 5;
            ModularAddConstantConstantModulusExhaustiveTestHelper (ModularAddConstantConstantModulusSimple, nQubits);
        }
    }

    ///////////////// MODULAR MULTIPLICATION WITH CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Reversible, out-of-place modular multiplication of two integers modulo
    /// a constant integer modulus. Given two n-bit integers x and y encoded in 
    /// LittleEndian registers `xs` and `ys`, and a constant integer `modulus`, the operation
    /// computes the product x*y mod modulus. The result is held in the third register `zs`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the first integer $x$.
    /// ## ys
    /// Qubit register encoding the second integer $y$.
    /// ## zs
    /// Qubit register for the result. Must be
    /// in state |0> initially.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularMulDblAddConstantModulus
    operation ModularMultiplierConstantModulusTestHelper( 
        ModularMultiplier : ( (BigInt, LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), 
        multiplier1 : BigInt, 
        multiplier2 : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[3 * nQubits]) {
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                mutable actualr = 0L;
                let multiplier1LE = LittleEndian(register[0 .. nQubits - 1]);
                let multiplier2LE = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
                let resultLE = LittleEndian(register[2 * nQubits .. 3 * nQubits - 1]); 
 
                // Write to qubit reigsters
                ApplyXorInPlaceL(multiplier1, multiplier1LE);
                ApplyXorInPlaceL(multiplier2, multiplier2LE);
                ApplyXorInPlaceL(0L, resultLE);

                // Run test
                ModularMultiplier(modulus, multiplier1LE, multiplier2LE, resultLE);
 
                // Compute classical expected result
                let prod = multiplier1 * multiplier2;
                let expected = (prod)% modulus;

                // Check results
                set actual1 = MeasureBigInteger(multiplier1LE);
                Fact(multiplier1==actual1, $"Expected {multiplier1}, got {actual1}");
                set actual2 = MeasureBigInteger(multiplier2LE);
                Fact(multiplier2== actual2, $"Expected {multiplier2}, got {actual2}");
                set actualr = MeasureBigInteger(resultLE);
                Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(multiplier1, multiplier1LE);
                        ApplyXorInPlaceL(multiplier2, multiplier2LE);
                        ApplyXorInPlaceL(0L, resultLE);

                        // controls are |0>, no multiplication is computed
                        // Run test
                        (Controlled ModularMultiplier) (controls, (modulus, multiplier1LE, multiplier2LE, resultLE));

                        // Check results
                        set actual1 = MeasureBigInteger(multiplier1LE);
                        Fact(multiplier1== actual1, $"Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureBigInteger(multiplier2LE);
                        Fact(multiplier2== actual2, $"Expected {multiplier2}, got {actual2}");                
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(0L== actualr, $"Expected {0}, got {actualr}");

                        // Write to qubit registers
                        ApplyXorInPlaceL(multiplier1, multiplier1LE);
                        ApplyXorInPlaceL(multiplier2, multiplier2LE);
                        ApplyXorInPlaceL(0L, resultLE);

                        // now controls are set to |1>, multiplication is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularMultiplier) (controls, (modulus, multiplier1LE, multiplier2LE, resultLE));

                        // Check results
                        set actual1 = MeasureBigInteger(multiplier1LE);
                        Fact(multiplier1== actual1, $"Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureBigInteger(multiplier2LE);
                        Fact(multiplier2== actual2, $"Expected {multiplier2}, got {actual2}");                
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

   operation ModularMultiplierConstantModulusExhaustiveTestHelper ( ModularMultiplier : ( (BigInt, LittleEndian, LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( multiplier1 in 0 .. modulus - 1 ) {
                    for( multiplier2 in 0 .. modulus - 1 ) {
                        ModularMultiplierConstantModulusTestHelper(ModularMultiplier, IntAsBigInt(multiplier1), IntAsBigInt(multiplier2), IntAsBigInt(modulus), nQubits);
                    }
                }
            }
        }
    }

    operation ModularMulDblAddConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let multiplier1 = 13L;
            let multiplier2 = 9L; 
            ModularMultiplierConstantModulusTestHelper(ModularMulDblAddConstantModulus, multiplier1, multiplier2, modulus, nQubits);
        }
    }

    operation ModularMulDblAddConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularMultiplierConstantModulusExhaustiveTestHelper (ModularMulDblAddConstantModulus, nQubits);
        }
    }

    operation ModularMulDblAddConstantModulusTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let multiplier1 = 13L;
            let multiplier2 = 42L; 
            ModularMultiplierConstantModulusTestHelper(ModularMulDblAddConstantModulus, multiplier1, multiplier2, modulus, nQubits);
        }
    }

    operation ModularMulDblAddConstantModulusExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;
            ModularMultiplierConstantModulusExhaustiveTestHelper (ModularMulDblAddConstantModulus, nQubits);
        }
    }

    ///////////////// MODULAR SQUARING WITH CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Reversible, out-of-place modular squaring of an integer modulo 
    /// a constant integer modulus. Given an n-bit integer x encoded in a LittleEndian 
    /// register `xs` and a constant integer `modulus`, the operation computes the square 
    /// x^2 = x*x mod modulus. The result is held in the register `zs`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## zs
    /// Qubit register for the result. The square 
    /// x^2 mod modulus will be xored into this register.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularSquDblAddConstantModulus
    operation ModularSquarerConstantModulusTestHelper( ModularSquarer : ( (BigInt, LittleEndian, LittleEndian) => Unit is Ctl), integer : BigInt, modulus : BigInt, nQubits : Int ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual = 0L;
                mutable actualr = 0L;
                let integerLE = LittleEndian(register[0 .. nQubits - 1]);
                let resultLE = LittleEndian(register[nQubits .. 2 * nQubits - 1]); 
 
                // Write to qubit register
                ApplyXorInPlaceL(integer, integerLE);
                ApplyXorInPlaceL(0L, resultLE);

                // Run test
                ModularSquarer(modulus, integerLE, resultLE);
 
                // Classical expected result
                let square = integer * integer;
                let expected = square % modulus;

                // Check results
                set actual = MeasureBigInteger(integerLE);
                Fact(integer==actual, $"Expected {integer}, got {actual}");
                set actualr = MeasureBigInteger(resultLE);
                Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);
                        ApplyXorInPlaceL(0L, resultLE);

                        // controls are |0>, no squaring is computed
                        // Run test
                        (Controlled ModularSquarer) (controls, (modulus, integerLE, resultLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Expected {integer}, got {actual}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(0L== actualr, $"Expected {0}, got {actualr}");

                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);
                        ApplyXorInPlaceL(0L, resultLE);

                        // now controls are set to |1>, squaring is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularSquarer) (controls, (modulus, integerLE, resultLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Expected {integer}, got {actual}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(expected== actualr, $"Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

   operation ModularSquarerConstantModulusExhaustiveTestHelper ( ModularSquarer : ( (BigInt, LittleEndian, LittleEndian) => Unit is Ctl), nQubits : Int ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    ModularSquarerConstantModulusTestHelper(ModularSquarer, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits);
                }
            }
        }
    }

    operation ModularSquDblAddConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            ModularSquarerConstantModulusTestHelper(ModularSquDblAddConstantModulus, integer, modulus, nQubits);
        }
    }

    operation ModularSquDblAddConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularSquarerConstantModulusExhaustiveTestHelper (ModularSquDblAddConstantModulus, nQubits);
        }
    }

    operation ModularSquDblAddConstantModulusTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let integer = 13L; 
            ModularSquarerConstantModulusTestHelper(ModularSquDblAddConstantModulus, integer, modulus, nQubits);
        }
    }

    operation ModularSquDblAddConstantModulusExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;
            ModularSquarerConstantModulusExhaustiveTestHelper (ModularSquDblAddConstantModulus, nQubits);
        }
    }

    ///////////////// MODULAR NEGATION WITH A CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Reversible, in-place modular negation of an integer modulo a constant
    /// integer modulus. Given an $n$-bit integer $x$ encoded in a LittleEndian register 
    /// `xs` and a constant integer `modulus`, the operation computes the negative  
    /// -x mod m. The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the integer x, is replaced with 
    /// the negative modulo `modulus`.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularNegConstantModulus
    operation ModularNegConstantModulusTestHelper(Negater : ((BigInt, LittleEndian) => Unit is Ctl + Adj), integer : BigInt, modulus : BigInt, nQubits : Int ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation 
            using (register = Qubit[nQubits]) {
                mutable actual1 = 0L;
                let integerLE = LittleEndian(register[0 .. nQubits - 1]);
 
                // Write to qubit register
                ApplyXorInPlaceL(integer, integerLE);

                // Run test
                Negater(modulus, integerLE);
 
                // Compute classical expected result
                let expected = (modulus - integer)%modulus;

                // Check results
                set actual1 = MeasureBigInteger(integerLE);
                Fact(expected== actual1, $"Expected {expected}, got {actual1}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);

                        // controls are |0>, no negation is computed
                        // Run test
                        (Controlled Negater) (controls, (modulus, integerLE));

                        // Check results
                        set actual1 = MeasureBigInteger(integerLE);
                        Fact(integer== actual1, $"Expected {integer}, got {actual1}");

                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled Negater) (controls, (modulus, integerLE));

                        // Check results
                        set actual1 = MeasureBigInteger(integerLE);
                        Fact(expected== actual1, $"Expected {expected}, got {actual1}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularNegConstantModulusExhaustiveTestHelper (Negater : ((BigInt, LittleEndian) => Unit is Ctl + Adj), nQubits : Int) : Unit {
        body (...) {
             for( modulus in 2^(nQubits-1) .. 2^nQubits - 1 ) {
                for( integer in 0 .. modulus - 1 ) {
                    ModularNegConstantModulusTestHelper(Negater, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits);
                }
            }
        }
    }

    operation ModularNegConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let integer = 111L; 
            ModularNegConstantModulusTestHelper(ModularNegConstantModulus, integer, modulus, nQubits);
        }
    }

    operation ModularNegConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;
            ModularNegConstantModulusExhaustiveTestHelper (ModularNegConstantModulus, nQubits);
        }
    }

    operation ModularNegConstantModulusTestReversible () : Unit {
        body (...) {
            let nQubits = 17;
            let modulus = 131071L;
            let integer = 31579L; 
            ModularNegConstantModulusTestHelper(ModularNegConstantModulus, integer, modulus, nQubits);
        }
    }

    operation ModularNegConstantModulusExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 5;
            ModularNegConstantModulusExhaustiveTestHelper(ModularNegConstantModulus, nQubits);
        }
    }

    ///////////////// MODULAR MULTIPLICATION BY A CONSTANT WITH A CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Reversible multiplication of an integer x in a quantum register by a classical
    /// integer c, modulo a classical integer m :  y = x*c mod m.
    /// Requires a register of 0 qubits to store the result.
    ///
    /// # Input
    /// ## modulus
    /// Classical modulus m
    /// ## constant
    /// Classical constant c to be multiplied
    /// ## xs
    /// Qubit register encoding the input integer x
    /// ## ys
    /// Qubit register for the output integer y
    /// 
    /// # Operations
    /// This can test:
    ///		* ModularMulByConstantConstantModulus
    operation ModularConstantMultipleConstantModulusTestHelper( 
        ModularConstantMultiplier : ( (BigInt, BigInt, LittleEndian, LittleEndian) => Unit is Ctl), 
        integer:BigInt, 
        constant : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual = 0L;
                mutable actualr = 0L;
                let integerLE = LittleEndian(register[0 .. nQubits - 1]);
                let resultLE = LittleEndian(register[nQubits .. 2 * nQubits - 1]); 
 
                // Write to qubit registers
                ApplyXorInPlaceL(integer, integerLE);
                ApplyXorInPlaceL(0L, resultLE);

                // Run test
                ModularConstantMultiplier(modulus, constant, integerLE, resultLE);
 
                // Compute clasical expected result
                let expected = (constant * integer) % modulus;

                // Check results
                set actual = MeasureBigInteger(integerLE);
                Fact(integer==actual, $"Non-controlled integer: Expected {integer}, got {actual}");
                set actualr = MeasureBigInteger(resultLE);
                Fact(expected== actualr, $"Non-controlled result: Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(integer, integerLE);
                        ApplyXorInPlaceL(0L, resultLE);

                        // controls are |0>, no squaring is computed
                        // Run test
                        (Controlled ModularConstantMultiplier) (controls, (modulus, constant, integerLE, resultLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Control-0 Integer: Expected {integer}, got {actual}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(0L== actualr, $"Control-0 Result: Expected {0}, got {actualr}");

                        // Write to qubit registers
                        ApplyXorInPlaceL(integer, integerLE);
                        ApplyXorInPlaceL(0L, resultLE);

                        // now controls are set to |1>, squaring is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularConstantMultiplier) (controls, (modulus, constant, integerLE, resultLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Control-1 Integer: Expected {integer}, got {actual}");
                        set actualr = MeasureBigInteger(resultLE);
                        Fact(expected== actualr, $"Control-1 Result: Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularConstantMultipleConstantModulusExhaustiveTestHelper ( 
        ModularConstantMultiplier : ( (BigInt, BigInt, LittleEndian, LittleEndian) => Unit is Ctl), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    for( constant in 0 .. modulus - 1 ) {
                        ModularConstantMultipleConstantModulusTestHelper(
                            ModularConstantMultiplier, 
                            IntAsBigInt(integer), 
                            IntAsBigInt(constant), 
                            IntAsBigInt(modulus), 
                            nQubits
                        );
                    }
                }
            }
        }
    }

    operation ModularConstantMultipleConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            let constant = 4L;
            ModularConstantMultipleConstantModulusTestHelper(ModularMulByConstantConstantModulus, integer, constant, modulus, nQubits);
        }
    }

    operation ModularConstantMultipleConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;//Roughly 18 seconds
            ModularConstantMultipleConstantModulusExhaustiveTestHelper (ModularMulByConstantConstantModulus, nQubits);
        }
    }

    ///////////////// MODULAR MULTIPLICATION BY A CONSTANT, IN PLACE, BY A CONSTANT MODULUS /////////////////
    ///
    /// # Summary
    /// Multiplies in-place a quantum integer x by a classical constant
    /// c, modulo a classical constant m.
    /// It borrows Length(x) qubits for the computation.
    ///
    /// # Input
    /// ## modulus
    /// Classical modulus m.
    /// ## constant
    /// Classical constant c to be multiplied. 
    /// Must be coprime to the modulus.
    /// ## xs
    /// Qubit register encoding the input integer x.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularMulByConstantConstantModulusInPlace
    operation ModularMultiplyInPlaceTestHelper( 
        ModularConstantMultiplier : ( (BigInt, BigInt, LittleEndian) => Unit is Ctl), 
        integer:BigInt, 
        constant : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[nQubits]) {
                mutable actual = 0L;
                let integerLE = LittleEndian(register[0 .. nQubits - 1]);
 
                // Write to qubit register
                ApplyXorInPlaceL(integer, integerLE);

                // Run test
                ModularConstantMultiplier(modulus, constant, integerLE);
 
                // Compute expected classical results
                let expected = (constant * integer) % modulus;

                // Check results
                set actual = MeasureBigInteger(integerLE);
                Fact(expected==actual, $"Non-controlled Result: Expected {integer}, got {actual}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);

                        // controls are |0>, no squaring is computed
                        // Run test
                        (Controlled ModularConstantMultiplier) (controls, (modulus, constant, integerLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Control-0 Result: Expected {integer}, got {actual}");

                        // Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);

                        // now controls are set to |1>, squaring is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularConstantMultiplier) (controls, (modulus, constant, integerLE));

                        // Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(expected== actual, $"Control-1 Result: Expected {integer}, got {actual}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularMultiplyInPlaceExhaustiveTestHelper ( 
        ModularConstantMultiplier : ( (BigInt, BigInt, LittleEndian) => Unit is Ctl), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 1 .. modulus - 1 ) {
                    for( constant in 1 .. modulus - 1 ) {
                        if (GreatestCommonDivisorI(integer, constant)==1){
                            ModularMultiplyInPlaceTestHelper(
                                ModularConstantMultiplier, 
                                IntAsBigInt(integer), 
                                IntAsBigInt(constant), 
                                IntAsBigInt(modulus), 
                                nQubits
                            );
                        }
                    }
                }
            }
        }
    }

    operation ModularMultiplyInPlaceConstantModulusTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            let constant = 4L;
            ModularMultiplyInPlaceTestHelper(ModularMulByConstantConstantModulusInPlace, integer, constant, modulus, nQubits);
        }
    }

    operation ModularMultiplyInPlaceConstantModulusExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;//Roughly 18 seconds
            ModularMultiplyInPlaceExhaustiveTestHelper (ModularMulByConstantConstantModulusInPlace, nQubits);
        }
    }

    ///////////////// MODULAR MULTIPLICATION IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Reversible, out-of-place modular multiplication of two integers modulo
    /// a constant integer modulus, represented in Montgomery form. Result is copied
    /// to a blank third register.
    ///
    /// # Description
    ///	Given two n-bit integers x and y encoded in MontModInt registers `xs` and `ys`,
    /// and a  constant integer `modulus`, the operation computes the product 
    /// x*y mod modulus. The result is held in the third register `blankOutput`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qbit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y.
    /// ## blankOutput
    /// Qubit register for the result. Must be
    /// in state $\ket{0}$ initially.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularMulMontgomeryFormGeneric
    ///
    /// # Remarks
    /// This must be separate from the test for constant 
    /// multiplication because the inputs are a different type, and
    /// must be adjusted to compare to classical
    operation ModularMultiplierMontgomeryFormTestHelper( 
        ModularMultiplier : ( ((MontModInt=> Unit is Ctl + Adj), MontModInt, MontModInt) => Unit is Ctl + Adj), 
        multiplier1 : BigInt, 
        multiplier2 : BigInt, 
        output : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[3 * nQubits]) {
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                mutable actualr = 0L;

                // Write to qubit registers
                let multiplier1MMI = CreateBigIntInMontgomeryForm(modulus, multiplier1, LittleEndian(register[0 .. nQubits - 1]));
                let multiplier2MMI = CreateBigIntInMontgomeryForm(modulus, multiplier2, LittleEndian(register[nQubits .. 2 * nQubits - 1]));
                let resultMMI = CreateBigIntInMontgomeryForm(modulus, output, LittleEndian(register[2 * nQubits .. 3 * nQubits - 1])); 

                // Run test
                ModularMultiplier(CopyMontModInt(_, resultMMI), multiplier1MMI, multiplier2MMI);
 
                // Compute expected classical result
                let prod = (multiplier1 * multiplier2 * 2L^nQubits)%modulus;
                let expectednonmont = prod ^^^ ((output * 2L^nQubits)%modulus);
                let expected = (InverseModL(2L^nQubits, modulus) * expectednonmont)%modulus;

                // Check results
                set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                Fact(multiplier1==actual1, $"Expected {multiplier1} as first multiplier, got {actual1}");
                set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                Fact(multiplier2== actual2, $"Expected {multiplier2} as second multiplier, got {actual2}");
                set actualr = MeasureMontgomeryInteger(resultMMI);
                Fact(expected== actualr, $"Expected {expected} as product, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                        EncodeBigIntInMontgomeryForm(output, resultMMI);

                        // controls are |0>, no multiplication is computed
                        // Run test
                        (Controlled ModularMultiplier) (controls, (CopyMontModInt(_, resultMMI), multiplier1MMI, multiplier2MMI));

                        // Check results
                        set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                        Fact(multiplier1== actual1, $"Control 0: Expected {multiplier1} as first multiplier, got {actual1}");
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(multiplier2== actual2, $"Control 0: Expected {multiplier2} as first multiplier, got {actual2}");                
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(output== actualr, $"Control 0: Expected {output}, got {actualr} as product");

                        // Write to qubit registers 
                        EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                        EncodeBigIntInMontgomeryForm(output, resultMMI);

                        // now controls are set to |1>, multiplication is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularMultiplier) (controls, (CopyMontModInt(_, resultMMI), multiplier1MMI, multiplier2MMI));

                        // Check result
                        set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                        Fact(multiplier1== actual1, $"Control 1: Expected {multiplier1} as first multiplier, got {actual1}");
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(multiplier2== actual2, $"Control 1: Expected {multiplier2} as first multiplier, got {actual2}");                
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(expected== actualr, $"Control 1: Expected {expected} as product, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

   operation ModularMultiplierMontgomeryFormExhaustiveTestHelper ( 
        ModularMultiplier : ( ((MontModInt=> Unit is Ctl + Adj), MontModInt, MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( multiplier1 in 0 .. modulus - 1 ) {
                    for( multiplier2 in 0 .. modulus - 1 ) {
                        for ( output in 0 .. modulus - 1 ){
                            ModularMultiplierMontgomeryFormTestHelper(
                                ModularMultiplier, 
                                IntAsBigInt(multiplier1), 
                                IntAsBigInt(multiplier2), 
                                IntAsBigInt(output), 
                                IntAsBigInt(modulus), 
                                nQubits
                            );
                        }
                    }
                }
            }
        }
    }

    operation ModularMulMontgomeryFormTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let multiplier1 = 13L;
            let multiplier2 = 9L; 
            let output = 3L;
            ModularMultiplierMontgomeryFormTestHelper(ModularMulMontgomeryFormGeneric, multiplier1, multiplier2, output, modulus, nQubits);
        }
    }

    operation ModularMulMontgomeryFormExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;//about 9 seconds
            ModularMultiplierMontgomeryFormExhaustiveTestHelper (ModularMulMontgomeryFormGeneric, nQubits);
        }
    }

    operation ModularMulMontgomeryFormTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let multiplier1 = 13L;
            let multiplier2 = 42L; 
            let output = 4L;
            ModularMultiplierMontgomeryFormTestHelper(ModularMulMontgomeryFormGeneric, multiplier1, multiplier2, output, modulus, nQubits);
        }
    }

    operation ModularMulMontgomeryFormExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 5;//about 22 seconds
            ModularMultiplierMontgomeryFormExhaustiveTestHelper (ModularMulMontgomeryFormWindowedGeneric, nQubits);
        }
    }

    ///////////////// OPEN MODULAR MULTIPLICATION IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Multiplies two integers encoded in qubit registers in Montgomery
    /// form. Requires n + 2 clean ancilla which are returned dirty.
    ///
    /// #Inputs
    /// ## modulus
    /// The classical modulus.
    /// ## xs
    /// The first quantum input to the product.
    /// Returned unchanged.
    /// ## ys 
    /// The second quantum input to the product.
    /// Returned unchanged.
    /// ## ancillas
    /// Clean ancilla qubits that are returned dirty.
    /// ## blankOutputs
    /// The output register, expected to 
    /// contain zeros. After the computation it 
    /// will contain the product of xs*ys*$2^{-n}$.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularMulMontgomeryFormOpen
    operation ModularMulMontgomeryFormOpenTestHelper(
        ModularMultiplier: ( (MontModInt, MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        multiplier1 : BigInt, 
        multiplier2 : BigInt, 
        modulus : BigInt, 
        nQubits : Int, 
        nAncillas : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[3 * nQubits + nAncillas]){
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                mutable result  = 0L;
                mutable ancilla = 0L;
                let ancillas = register[3 * nQubits .. 3 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);

                // Write to qubit registers
                mutable multiplier1MMI = CreateBigIntInMontgomeryForm(modulus, multiplier1, LittleEndian(register[0..nQubits - 1]));
                mutable multiplier2MMI = CreateBigIntInMontgomeryForm(modulus, multiplier2, LittleEndian(register[nQubits .. 2 * nQubits - 1]));
                mutable resultMMI = MontModInt(modulus, LittleEndian(register[2 * nQubits .. 3 * nQubits - 1]));
                
                // Run test
                ModularMultiplier(multiplier1MMI, multiplier2MMI, ancillas, resultMMI);

                // Compute expected classical results
                let prod = (multiplier1 * multiplier2) % modulus;

                // Check results
                set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                Fact(actual1 == multiplier1, $"Input 1: Expected {multiplier1}, got {actual1}");
                set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                Fact(actual2 == multiplier2, $"Input 2: Expected {multiplier2}, got {actual2}");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == prod, $"Result: Expected {prod}, got {result}");

                // Write results to measured qubit registers
                EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                EncodeBigIntInMontgomeryForm(prod, resultMMI);
                
                // Uncompute test
                (Adjoint ModularMultiplier)(multiplier1MMI, multiplier2MMI, ancillas, resultMMI);

                // Check results
                set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                Fact(actual1 == multiplier1, $"Uncomputed: Input 1: Expected {multiplier1}, got {actual1}");
                set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                Fact(actual2 == multiplier2, $"Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == 0L, $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);

                        // Run test
                        (Controlled ModularMultiplier)(controls, (multiplier1MMI, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                        Fact(actual1 == multiplier1, $"Control 0: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 0: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Result: Expected 0, got {result}");

                        // Write results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);

                        // Uncompute tests
                        (Controlled Adjoint ModularMultiplier)(controls, (multiplier1MMI, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                        Fact(actual1 == multiplier1, $"Control 0: Uncomputed: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 0: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);

                        // Run test
                        (Controlled ModularMultiplier)(controls, (multiplier1MMI, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                        Fact(actual1 == multiplier1, $"Control 1: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 1: Input 2: Expected {multiplier2}, got {actual2}");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == prod, $"Control 1: Result: Expected {prod}, got {result}");

                        // Write results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier1, multiplier1MMI);
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                        EncodeBigIntInMontgomeryForm(prod, resultMMI);

                        // Uncompute test
                        (Controlled Adjoint ModularMultiplier)(controls, (multiplier1MMI, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual1 = MeasureMontgomeryInteger(multiplier1MMI);
                        Fact(actual1 == multiplier1, $"Control 1: Uncomputed: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 1: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularMultiplierMontgomeryFormOpenExhaustiveTestHelper ( 
        ModularMultiplier : ( (MontModInt, MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int , 
        nAncillas : Int
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( multiplier1 in 0 .. modulus - 1 ) {
                    for( multiplier2 in 0 .. modulus - 1 ) {
                        ModularMulMontgomeryFormOpenTestHelper(
                            ModularMultiplier, 
                            IntAsBigInt(multiplier1), 
                            IntAsBigInt(multiplier2), 
                            IntAsBigInt(modulus), 
                            nQubits, 
                            nAncillas
                        );
                    }
                }
            }
        }
    }

    operation ModularMultiplierMontgomeryFormOpenRandomTestHelper ( 
        ModularMultiplier : ( (MontModInt, MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int , 
        nAncillas : Int,
        nTests : Int
    ) : Unit {
        body (...) {
            for (idx in 0 .. nTests - 1){
                let modulus = 2L^(nQubits - 1) + 2L*RandomBigInt(2L^(nQubits - 2)) + 1L;
                let multiplier1 = RandomBigInt(modulus);
                let multiplier2 = RandomBigInt(modulus);
                ModularMulMontgomeryFormOpenTestHelper(
                    ModularMultiplier, 
                    multiplier1,
                    multiplier2,
                    modulus,
                    nQubits, 
                    nAncillas
                );
            }
        }
    }

    operation ModularMultiplierMontgomeryFormOpenTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let multiplier1 = 13L;
            let multiplier2 = 9L; 
            let (nAncillas, _) = AncillaCountModularMulMontgomeryForm(nQubits);
            ModularMulMontgomeryFormOpenTestHelper(ModularMulMontgomeryFormOpen, multiplier1, multiplier2, modulus, nQubits, nAncillas);
        }
    }

    operation ModularMultiplierMontgomeryFormOpenExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;//about 9 seconds
            let (nAncillas, _) = AncillaCountModularMulMontgomeryForm(nQubits);
            ModularMultiplierMontgomeryFormOpenExhaustiveTestHelper (ModularMulMontgomeryFormOpen, nQubits, nAncillas);
        }
    }

    operation ModularMultiplierMontgomeryFormOpenTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let multiplier1 = 13L;
            let multiplier2 = 42L; 

            let (nAncillas, _) = AncillaCountModularMulMontgomeryForm(nQubits);
            ModularMulMontgomeryFormOpenTestHelper(ModularMulMontgomeryFormOpen, multiplier1, multiplier2, modulus, nQubits, nAncillas);
        }
    }

    operation ModularMultiplierMontgomeryFormOpenExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;//about 22 seconds
            
            let (nAncillas, _) = AncillaCountModularMulMontgomeryForm(nQubits);
            ModularMultiplierMontgomeryFormOpenExhaustiveTestHelper (ModularMulMontgomeryFormOpen, nQubits, nAncillas);
        }
    }

     operation ModularMultiplierWindowedMontgomeryFormOpenRandomTestReversible () : Unit {
        body (...) {
            let nQubits = 6;//about 22 seconds
            let (nAncillas, _) = AncillaCountModularMulMontgomeryForm(nQubits);
            let windowSize = 4;
            let nTests = 1000;
            let multiplier = ModularMulMontgomeryFormWindowedOpen(windowSize, _, _, _, _);
            ModularMultiplierMontgomeryFormOpenRandomTestHelper (multiplier, nQubits, nAncillas, nTests);
        }
    }

    ///////////////// OPEN MODULAR MULTIPLICATION BY A CONSTANT IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Multiplies an integer encoded in a qubit register in Montgomery
    /// form by a classical integer, modulo another classical integer.
    /// Requires clean ancilla which are returned dirty.
    ///
    /// # Inputs
    /// ## constant
    /// The constant to be multiplied into the qubit register.
    /// ## xs
    /// The qubit register (as well as the constant modulus).
    /// ## ancilla
    /// Clean ancilla which are returned dirty.
    /// ## blankOutputs
    /// Qubit register which must be input as zeros, and will
    /// return the product
    ///
    /// # Operations
    /// This can test:
    ///		* MulByConstantMontgomeryFormOpen
    operation ModularMulConstantMontgomeryFormOpenTestHelper(
        ModularMultiplier: ( (BigInt, MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        multiplier1 : BigInt, 
        multiplier2 : BigInt, 
        modulus : BigInt, 
        nQubits : Int, 
        nAncillas : Int 
        ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits + nAncillas]){
                mutable actual2 = 0L;
                mutable result  = 0L;
                mutable ancilla = 0L;
                let ancillas = register[2 * nQubits .. 2 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable multiplier2MMI = CreateBigIntInMontgomeryForm(modulus, multiplier2, LittleEndian(register[0..nQubits - 1]));
                mutable resultMMI = MontModInt(modulus, LittleEndian(register[1 * nQubits .. 2 * nQubits - 1]));

                // Run test
                ModularMultiplier(multiplier1, multiplier2MMI, ancillas, resultMMI);

                // Compute classical expected result
                let prod = (multiplier1 * multiplier2) % modulus;

                // Check results
                set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                Fact(actual2 == multiplier2, $"Input 1: Expected {multiplier2}, got {actual2}");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == prod, $"Result: Expected {prod}, got {result}");

                // Write results into measured qubit registers
                EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                EncodeBigIntInMontgomeryForm(prod, resultMMI);

                // Uncompute test
                (Adjoint ModularMultiplier)(multiplier1, multiplier2MMI, ancillas, resultMMI);

                // Check results
                set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                Fact(actual2 == multiplier2, $"Uncomputed: Input 1: Expected {multiplier2}, got {actual2}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == 0L, $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);

                        // run test
                        (Controlled ModularMultiplier)(controls, (multiplier1, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 0: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Result: Expected 0, got {result}");

                        // Write results to measured qubit register
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);

                        // Uncompute test
                        (Controlled Adjoint ModularMultiplier)(controls, (multiplier1, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 0: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);

                        // Run test
                        (Controlled ModularMultiplier)(controls, (multiplier1, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 1: Input 2: Expected {multiplier2}, got {actual2}");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == prod, $"Control 1: Result: Expected {prod}, got {result}");

                        // Encode results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                        EncodeBigIntInMontgomeryForm(prod, resultMMI);

                        // Uncompute test
                        (Controlled Adjoint ModularMultiplier)(controls, (multiplier1, multiplier2MMI, ancillas, resultMMI));

                        // Check results
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(actual2 == multiplier2, $"Control 1: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularMultiplierConstantMontgomeryFormOpenExhaustiveTestHelper ( 
        ModularMultiplier : ( (BigInt, MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int, 
        nAncillas : Int
        ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( multiplier1 in 0 .. modulus - 1 ) {
                    for( multiplier2 in 0 .. modulus - 1 ) {
                        ModularMulConstantMontgomeryFormOpenTestHelper(
                            ModularMultiplier, 
                            IntAsBigInt(multiplier1), 
                            IntAsBigInt(multiplier2), 
                            IntAsBigInt(modulus), 
                            nQubits, 
                            nAncillas
                        );
                    }
                }
            }
        }
    }

    operation ModularMultiplierConstantMontgomeryFormOpenTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let multiplier1 = 13L;
            let multiplier2 = 9L; 
            let (nAncillas, _) = AncillaCountConstantMulMontgomeryForm(nQubits);
            ModularMulConstantMontgomeryFormOpenTestHelper(MulByConstantMontgomeryFormOpen, multiplier1, multiplier2, modulus, nQubits, nAncillas);
        }
    }

    operation ModularMultiplierConstantMontgomeryFormOpenExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;//about 9 seconds
            let (nAncillas, _) = AncillaCountConstantMulMontgomeryForm(nQubits);
            ModularMultiplierConstantMontgomeryFormOpenExhaustiveTestHelper (MulByConstantMontgomeryFormOpen, nQubits, nAncillas);
        }
    }

    operation ModularMultiplierConstantMontgomeryFormOpenTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let multiplier1 = 13L;
            let multiplier2 = 42L; 

            let (nAncillas, _) = AncillaCountConstantMulMontgomeryForm(nQubits);
            ModularMulConstantMontgomeryFormOpenTestHelper(MulByConstantMontgomeryFormOpen, multiplier1, multiplier2, modulus, nQubits, nAncillas);
        }
    }

    operation ModularMultiplierConstantMontgomeryFormOpenExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;//about 2 seconds
            
            let (nAncillas, _) = AncillaCountConstantMulMontgomeryForm(nQubits);
            ModularMultiplierConstantMontgomeryFormOpenExhaustiveTestHelper (MulByConstantMontgomeryFormOpen, nQubits, nAncillas);
        }
    }

    ///////////////// MODULAR MULTIPLICATION BY A CONSTANT IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Multiplies a quantum register by a classical constant
    /// modulo a classical modulus, 
    /// with a built-in Montgomery reduction by a factor of $2^{-n}$, 
    /// where $n$ is the number of qubits for each input.
    ///
    /// It processes the output with an operation passed by 
    /// the user, before uncomputing the multiplication.
    ///
    /// #Inputs
    /// ## copyop
    /// The operation will give `copyop` the register $\ket{x*y mod m}$
    /// as input, and assumes that `copyop` leaves the input
    /// register unchanged.
    /// ## constant
    /// The classical input to the product
    /// ## xs 
    /// The quantum input to the product.
    /// Returned unchanged.
    ///
    /// # Operations
    /// This can test:
    ///		* MulByConstantMontgomeryFormGeneric
    operation ModularConstantMultiplierMontgomeryFormTestHelper( 
        ModularMultiplier : ( ((MontModInt=> Unit is Ctl + Adj), BigInt, MontModInt) => Unit is Ctl + Adj), 
        multiplier1 : BigInt, 
        multiplier2 : BigInt, 
        output : BigInt, 
        modulus : BigInt, 
        nQubits : Int ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                mutable actualr = 0L;

                // Write to qubit registers
                let multiplier2MMI = CreateBigIntInMontgomeryForm(modulus, multiplier2, LittleEndian(register[0 .. nQubits - 1]));
                let resultMMI = CreateBigIntInMontgomeryForm(modulus, output, LittleEndian(register[1 * nQubits .. 2 * nQubits - 1])); 

                // Run test
                ModularMultiplier(ModularAddMontgomeryForm(_, resultMMI), multiplier1, multiplier2MMI);
 
                // Compute expected classical result
                let prod = (multiplier1 * multiplier2) % modulus;
                let expected = (prod + output) % modulus;

                // Check results
                set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                Fact(multiplier2== actual2, $"Expected {multiplier2} as second multiplier, got {actual2}");
                set actualr = MeasureMontgomeryInteger(resultMMI);
                Fact(expected== actualr, $"Expected {expected} as product, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                        EncodeBigIntInMontgomeryForm(output, resultMMI);

                        // controls are |0>, no multiplication is computed
                        // Run test
                        (Controlled ModularMultiplier) (controls, (ModularAddMontgomeryForm(_, resultMMI), multiplier1, multiplier2MMI));

                        // Check results
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(multiplier2== actual2, $"Control 0: Expected {multiplier2} as first multiplier, got {actual2}");                
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(output== actualr, $"Control 0: Expected {output}, got {actualr} as product");

                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(multiplier2, multiplier2MMI);
                        EncodeBigIntInMontgomeryForm(output, resultMMI);

                        // now controls are set to |1>, multiplication is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularMultiplier) (controls, (ModularAddMontgomeryForm(_, resultMMI), multiplier1, multiplier2MMI));

                        // Check results
                        set actual2 = MeasureMontgomeryInteger(multiplier2MMI);
                        Fact(multiplier2== actual2, $"Control 1: Expected {multiplier2} as first multiplier, got {actual2}");                
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(expected== actualr, $"Control 1: Expected {expected} as product, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }
      operation ModularMultiplyConstantMontgomeryFormExhaustiveTestHelper ( 
        ModularMultiplier : ( ((MontModInt=> Unit is Ctl + Adj), BigInt, MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( multiplier1 in 0 .. modulus - 1 ) {
                    for( multiplier2 in 0 .. modulus - 1 ) {
                        for ( output in 0 .. modulus - 1 ){
                            ModularConstantMultiplierMontgomeryFormTestHelper(
                                ModularMultiplier, 
                                IntAsBigInt(multiplier1), 
                                IntAsBigInt(multiplier2), 
                                IntAsBigInt(output), 
                                IntAsBigInt(modulus), 
                                nQubits
                            );
                        }
                    }
                }
            }
        }
    }

    operation ModularMultiplyConstantMontgomeryFormTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let multiplier1 = 13L;
            let multiplier2 = 9L; 
            let output = 3L;
            ModularConstantMultiplierMontgomeryFormTestHelper(MulByConstantMontgomeryFormGeneric, multiplier1, multiplier2, output, modulus, nQubits);
        }
    }

    operation ModularMultiplyConstantMontgomeryFormExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;//about 9 seconds
            ModularMultiplyConstantMontgomeryFormExhaustiveTestHelper (MulByConstantMontgomeryFormGeneric, nQubits);
        }
    }

    operation ModularMultiplyConstantMontgomeryFormTestReversible () : Unit {
        body (...) {
            let nQubits = 7;
            let modulus = 127L;
            let multiplier1 = 13L;
            let multiplier2 = 42L; 
            let output = 4L;
            ModularConstantMultiplierMontgomeryFormTestHelper(MulByConstantMontgomeryFormGeneric, multiplier1, multiplier2, output, modulus, nQubits);
        }
    }

    operation ModularMultiplyConstantMontgomeryFormExhaustiveTestReversible () : Unit {
        body (...) {
            let nQubits = 4;//about 50 seconds
            ModularMultiplyConstantMontgomeryFormExhaustiveTestHelper (MulByConstantMontgomeryFormGeneric, nQubits);
        }
    }

    ///////////////// MODULAR INVERSION IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Computes the modular inverse of xs into xsinv, using
    /// a bit-shift version of the Extended Euclidean Algorithm.
    ///
    /// # Inputs
    /// ## copyop
    /// An operation that will perform some action on whatever
    /// is in the LittleEndian register in its argument.
    /// This is expected to be some sort of copy to the 
    /// same register as `outputs`.
    /// `copyop` MUST commute with modular multiplication 
    /// for a well-defined result (e.g., modular addition
    /// but not XOR).
    /// ## doubleop
    /// Operation that will double the output register.
    /// This is used to counteract the doubling used
    /// to correct the output from the inversion algorithm.
    /// ## xs
    /// The input to be inverted
    /// ## outputs
    /// The output that will contain the inverse
    ///
    /// # Operations
    /// This can test:
    ///		* InvertBitShiftConstantModulusGeneric
    operation ModularInvMontgomeryFormTestHelper( 
        ModularInverter : ( (MontModInt, MontModInt) => Unit is Ctl), 
        integer : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual = 0L;
                mutable actualr = 0L;

                // Write to qubit registers
                let integerMMI = CreateBigIntInMontgomeryForm(modulus, integer, LittleEndian(register[0 .. nQubits - 1]));
                let resultMMI = CreateBigIntInMontgomeryForm(modulus, 0L, LittleEndian(register[nQubits .. 2 * nQubits - 1])); 
 
                // Run test
                ModularInverter( integerMMI, resultMMI);
 
                // Compute expected classical result
                let inverse = InverseModL(integer, modulus);
                let expected = (inverse)%modulus;

                // Check results
                set actual = MeasureMontgomeryInteger(integerMMI);
                Fact(integer==actual, $"Input: Expected {integer}, got {actual}");
                set actualr = MeasureMontgomeryInteger(resultMMI);
                Fact(expected== actualr, $"Inverse: Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(integer, integerMMI);
                        EncodeBigIntInMontgomeryForm(0L, resultMMI);

                        // controls are |0>, no squaring is computed
                        // Run test
                        (Controlled ModularInverter) (controls, (integerMMI, resultMMI));

                        // Check result
                        set actual = MeasureMontgomeryInteger(integerMMI);
                        Fact(integer== actual, $"Controlled by 0: Input: Expected {integer}, got {actual}");
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(0L== actualr, $"Controlled by 1: Inverse: Expected {0}, got {actualr}");

                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(integer, integerMMI);
                        EncodeBigIntInMontgomeryForm(0L, resultMMI);

                        // now controls are set to |1>, squaring is computed
                        ApplyToEach(X, controls);
        
                        // Run test
                        (Controlled ModularInverter) (controls, (integerMMI, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(integerMMI);
                        Fact(integer== actual, $"Controlled by 1: Input: Expected {integer}, got {actual}");
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(expected== actualr, $"Controlled by 1: Inverse: Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularInvMontgomeryFormExhaustiveTestHelper ( ModularInverter : ( (MontModInt, MontModInt) => Unit is Ctl), nQubits : Int ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer1 in 0 .. modulus - 1 ) {
                    if (GreatestCommonDivisorI(modulus, integer1)==1){
                        ModularInvMontgomeryFormTestHelper(ModularInverter, IntAsBigInt(integer1), IntAsBigInt(modulus), nQubits);
                    }
                }
            }
        }
    }

    operation ModularInvMontgomeryFormTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer1 = 13L;
            ModularInvMontgomeryFormTestHelper(ModularInvertAndCopyMontgomeryForm, integer1, modulus, nQubits);
        }
    }

    operation ModularInvMontgomeryFormExhaustiveTest () : Unit {
        body (...) {
          //  let nQubits = 4; //2 seconds
            let nQubits = 5; //4 seconds
            ModularInvMontgomeryFormExhaustiveTestHelper (ModularInvertAndCopyMontgomeryForm, nQubits);
        }
    }


    ///////////////// MODULAR DIVISION IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Given three qubit registers `xs`, `ys`, and `outputs` containing modular integers in 
    /// Montgomery form, computes the inverse of xs, multiplies the result by ys, and adds
    /// the product to `outputs` (in place), return the result in Montgomery form.
    ///
    /// # Inputs
    /// ## xs
    /// MontModInt containing the number to be inverted
    /// ## ys
    /// MontModInt containing the number to multiply by xs
    /// ## outputs
    /// MontModInt where the result will be added and output
    ///
    /// # Operations
    /// This can test:
    ///		* ModularDivideAndAddMontgomeryForm
    operation ModularDivideMontgomeryFormTestHelper( 
        ModularDivider : ( (MontModInt, MontModInt, MontModInt) => Unit is Ctl), 
        modulus : BigInt, 
        invertand : BigInt, 
        multiplicand : BigInt, 
        summand : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[3 * nQubits]) {
                mutable actuali = 0L;
                mutable actualm = 0L;
                mutable actuals = 0L;

                // Write to qubit registers
                let invertandMMI = CreateBigIntInMontgomeryForm(modulus, invertand, LittleEndian(register[0 .. nQubits - 1]));
                let multiplicandMMI = CreateBigIntInMontgomeryForm(modulus, multiplicand, LittleEndian(register[nQubits..2 * nQubits-1]));
                let summandMMI = CreateBigIntInMontgomeryForm(modulus, summand, LittleEndian(register[2 * nQubits .. 3 * nQubits - 1])); 
                
                // Run test
                ModularDivider( invertandMMI, multiplicandMMI, summandMMI);
 
                // Compute expected classical result
                let inverse = InverseModL(invertand, modulus);
                let product = (inverse * multiplicand) % modulus;
                let sum = (product + summand) % modulus;

                // Check results
                set actuali = MeasureMontgomeryInteger(invertandMMI);
                Fact(invertand==actuali, $"Invertand: Expected {invertand}, got {actuali}");
                set actualm = MeasureMontgomeryInteger(multiplicandMMI);
                Fact(multiplicand== actualm, $"Multiplicand: Expected {multiplicand}, got {actualm}");
                set actuals = MeasureMontgomeryInteger(summandMMI);
                Fact(sum== actuals, $"Result: Expected {sum}, got {actuals}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(invertand, invertandMMI);
                        EncodeBigIntInMontgomeryForm(multiplicand, multiplicandMMI);
                        EncodeBigIntInMontgomeryForm(summand, summandMMI);

                        // controls are |0>, no dividing is computed
                        // Run test
                        (Controlled ModularDivider) (controls, (invertandMMI, multiplicandMMI, summandMMI));

                        // Check result
                        set actuali = MeasureMontgomeryInteger(invertandMMI);
                        Fact(invertand==actuali, $"Control 0: Invertand: Expected {invertand}, got {actuali}");
                        set actualm = MeasureMontgomeryInteger(multiplicandMMI);
                        Fact(multiplicand== actualm, $"Control 0: Multiplicand: Expected {multiplicand}, got {actualm}");
                        set actuals = MeasureMontgomeryInteger(summandMMI);
                        Fact(actuals== summand, $"Control 0: Result: Expected {summand}, got {actuals}");

                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(invertand, invertandMMI);
                        EncodeBigIntInMontgomeryForm(multiplicand, multiplicandMMI);
                        EncodeBigIntInMontgomeryForm(summand, summandMMI);

                        // now controls are set to |1>, dividing is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularDivider) (controls, (invertandMMI, multiplicandMMI, summandMMI));

                        // Check results
                        set actuali = MeasureMontgomeryInteger(invertandMMI);
                        Fact(invertand==actuali, $"Control 1: Invertand: Expected {invertand}, got {actuali}");
                        set actualm = MeasureMontgomeryInteger(multiplicandMMI);
                        Fact(multiplicand== actualm, $"Control 1: Multiplicand: Expected {multiplicand}, got {actualm}");
                        set actuals = MeasureMontgomeryInteger(summandMMI);
                        Fact(sum== actuals, $"Control 1: Result: Expected {sum}, got {actuals}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularDivideMontgomeryFormExhaustiveTestHelper ( 
        ModularDivider : ( (MontModInt, MontModInt, MontModInt) => Unit is Ctl), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( invertand in 1 .. modulus - 1 ) {
                    if (GreatestCommonDivisorI(modulus, invertand)==1){
                        for( multiplicand in 0 .. modulus - 1 ) {
                            for( summand in 0 .. modulus - 1 ) {
                                ModularDivideMontgomeryFormTestHelper(
                                    ModularDivider, 
                                    IntAsBigInt(modulus), 
                                    IntAsBigInt(invertand), 
                                    IntAsBigInt(multiplicand), 
                                    IntAsBigInt(summand), 
                                    nQubits
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    operation ModularDivMontgomeryFormTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 13L;
            let invertand = 4L;
            let multiplicand = 5L;
            let summand = 2L;
            ModularDivideMontgomeryFormTestHelper(ModularDivideAndAddMontgomeryForm, modulus, invertand, multiplicand, summand, nQubits);
        }
    }

    operation ModularDivMontgomeryFormTestReversible () : Unit {
        body (...) {
            let nQubits = 192;
            let modulus = 98173098607649268658151980872992366641748671760350709279L;
            let invertand = 22394683263204398402443466307380211523332179104093427200L;
            let multiplicand = 614911202705938193475341563320076079441408231768203200L;
            let summand = 25925232139992086205324078950339757021400380768779673000L;
            ModularDivideMontgomeryFormTestHelper(ModularDivideAndAddMontgomeryForm, modulus, invertand, multiplicand, summand, nQubits);
        }
    }

    operation ModularDivMontgomeryFormExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 3;// about 30 seconds
        //    let nQubits = 4; //about 13 minutes
            ModularDivideMontgomeryFormExhaustiveTestHelper (ModularDivideAndAddMontgomeryForm, nQubits);
        }
    }

    /// # Summary
    /// Tests a range of qubit register sizes
    /// and tests 300 random divisions at that size.
    operation ModularDivMontgomeryFormLargeTestReversible () : Unit {
        body (...) {
            let nTests = 2;
            for (nQubits in 6..192){
                Message($"{nQubits} qubits:");
                mutable idxTest = 0;
                while (idxTest <= nTests){
                    let modulus = 2L * RandomBigInt(2L ^ (nQubits - 1)) + 1L;
                    let invertand = RandomBigInt(modulus);
                    if (GreatestCommonDivisorL(invertand, modulus)==1L and modulus>2L){
                        let multiplicand = RandomBigInt(modulus);
                        let summand = RandomBigInt(modulus);
                        ModularDivideMontgomeryFormTestHelper(ModularDivideAndAddMontgomeryForm, modulus, invertand, multiplicand, summand, nQubits);
                        set idxTest = idxTest+1;
                    }
                }
            }
        }
    }

    ///////////////// OPEN MODULAR INVERSION IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Computes the modular inverse of an integer encoded in Montgomery
    /// form in a quantum register, and copies the results to an output.
    /// Takes clean ancilla and returns them dirty, and modifies the input.
    ///
    /// # Inputs
    /// ## xs
    /// Modular integer to be inverted. Returned in an undetermined state.
    /// ## ancillas
    /// Ancilla array that must be clean as input, and is returned dirty.
    /// ## blankOutputs
    /// Qubit register assumed to be 0 which will store the output.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularInvMontgomeryFormOpen
    operation ModularInvMontgomeryFormOpenTestHelper(
        Inverter: ( (MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        input : BigInt, 
        modulus : BigInt, 
        nQubits : Int, 
        nAncillas : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits + nAncillas]){
                mutable actual = 0L;
                mutable result  = 0L;
                mutable ancilla = 0L;
                let ancillas = register[2 * nQubits .. 2 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);

                // Write to qubit registers
                mutable inputMMI = CreateBigIntInMontgomeryForm(modulus, input, LittleEndian(register[0..nQubits - 1]));
                mutable resultMMI = MontModInt(modulus, LittleEndian(register[1 * nQubits .. 2 * nQubits - 1]));
                
                // Run tests
                Inverter(inputMMI, ancillas, resultMMI);

                // Compute classical expected result
                mutable inverse = 0L;
                if (not (input == 0L)){
                    set inverse = InverseModL(input, modulus);
                }

                // Check results
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == inverse, $"Result: Expected {inverse}, got {result}");

                // Write results to measured qubit registers
                EncodeBigIntInMontgomeryForm(inverse, resultMMI);

                // Uncompute test
                (Adjoint Inverter)(inputMMI, ancillas, resultMMI);

                // Check results:
                set actual = MeasureMontgomeryInteger(inputMMI);
                Fact(actual == input, $"Uncomputed: Input: Expected {input}, got {actual}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == 0L, $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        EncodeBigIntInMontgomeryForm(input, inputMMI);

                        // Run test
                        (Controlled Inverter)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results 
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 0: Input: Expected {input}, got {actual}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Result: Expected 0, got {result}");

                        // Write results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(input, inputMMI);

                        // Uncompute test
                        (Controlled Adjoint Inverter)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 0: Uncomputed: Input: Expected {input}, got {actual}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeBigIntInMontgomeryForm(input, inputMMI);

                        // Run test
                        (Controlled Inverter)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == inverse, $"Control 1: Result: Expected {inverse}, got {result}");

                        // Write results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(inverse, resultMMI);

                        // Uncompute test
                        (Controlled Adjoint Inverter)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 1: Uncomputed: Input 1: Expected {input}, got {actual}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }



    operation ModularInvMontgomeryFormOpenExhaustiveTestHelper ( 
        ModularInverter : ( (MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int, 
        nAncillas : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    if (GreatestCommonDivisorI(integer, modulus)==1 or integer==0){
                        ModularInvMontgomeryFormOpenTestHelper(ModularInverter, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits, nAncillas);
                    }
                }
            }
        }
    }

    operation ModularInvMontgomeryFormOpenTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            let summand = 4L;
            let logn = BitSizeI(nQubits);
            let nAncillas = 2 * nQubits + logn + 2;
            ModularInvMontgomeryFormOpenTestHelper(ModularInvMontgomeryFormOpen, integer, modulus, nQubits, nAncillas);
        }
    }

    operation ModularInvMontgomeryFormOpenExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 4;
            // let nQubits = 5;//about 5 minutes
            let logn = BitSizeI(nQubits);
            let (nAncillas, _) = AncillaCountModularInvMontgomeryForm(nQubits);
            ModularInvMontgomeryFormOpenExhaustiveTestHelper (ModularInvMontgomeryFormOpen, nQubits, nAncillas);
        }
    }

    ///////////////// MODULAR SQUARING AND ADDING IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Squares an integer modulo a classical
    /// modulus, using Montgomery mulitplication.
    /// The result is processed according to a 
    /// user-specified operation, then uncomputed.
    ///
    /// # Inputs
    /// ## copyop
    /// The operation applied to x^2 once it is
    /// computed, before it is uncomputed. It must
    /// not change the value in `xs`.
    /// ## xs
    /// Qubit register to be squared.
    ///
    /// # Operations
    /// This can test:
    ///		* ModularSquMontgomeryFormGeneric
    operation ModularSquAndAddMontgomeryFormTestHelper( 
        ModularSquarer : ( ((MontModInt => Unit is Ctl + Adj), MontModInt) => Unit is Ctl), 
        integer : BigInt, 
        summand : BigInt, 
        modulus : BigInt, 
        nQubits : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits]) {
                mutable actual = 0L;
                mutable actualr = 0L;

                // Write to qubit registers
                let integerMMI = CreateBigIntInMontgomeryForm(modulus, integer, LittleEndian(register[0..nQubits-1]));
                let resultMMI = CreateBigIntInMontgomeryForm(modulus, summand, LittleEndian(register[nQubits .. 2 * nQubits - 1])); 

                // Run test
                ModularSquarer(ModularAddMontgomeryForm(_, resultMMI), integerMMI);
 
                // Compute expected classical result
                let square = integer * integer;
                let expected = (square + summand) % modulus;

                // Check results
                set actual = MeasureMontgomeryInteger(integerMMI);
                Fact(integer==actual, $"Input: Expected {integer}, got {actual}");
                set actualr = MeasureMontgomeryInteger(resultMMI);
                Fact(expected== actualr, $"Result: Expected {expected}, got {actualr}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(integer, integerMMI);
                        EncodeBigIntInMontgomeryForm(summand, resultMMI); 

                        // controls are |0>, no squaring is computed
                        // Run test
                        (Controlled ModularSquarer) (controls, (ModularAddMontgomeryForm(_, resultMMI), integerMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(integerMMI);
                        Fact(integer== actual, $"Control 0: Input: Expected {integer}, got {actual}");
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(summand== actualr, $"Control 0: Result: Expected {0}, got {actualr}");

                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(integer, integerMMI);
                        EncodeBigIntInMontgomeryForm(summand, resultMMI); 

                        // now controls are set to |1>, squaring is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled ModularSquarer) (controls, (ModularAddMontgomeryForm(_, resultMMI), integerMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(integerMMI);
                        Fact(integer== actual, $"Control 1: Input: Expected {integer}, got {actual}");
                        set actualr = MeasureMontgomeryInteger(resultMMI);
                        Fact(expected== actualr, $"Control 1: Result: Expected {expected}, got {actualr}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

   operation ModularSquMontgomeryFormExhaustiveTestHelper ( 
        ModularSquarer : ( ((MontModInt => Unit is Ctl + Adj), MontModInt) => Unit is Ctl), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    for( summand in 0 .. modulus - 1 ){
                        ModularSquAndAddMontgomeryFormTestHelper(ModularSquarer, IntAsBigInt(integer), IntAsBigInt(summand), IntAsBigInt(modulus), nQubits);
                    }
                }
            }
        }
    }

    operation ModularSquMontgomeryFormTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            let summand = 4L;
            ModularSquAndAddMontgomeryFormTestHelper(ModularSquMontgomeryFormGeneric, integer, summand, modulus, nQubits);
        }
    }

    operation ModularSquMontgomeryFormExhaustiveTest () : Unit {
        body (...) {    
            //let nQubits = 3;
            let nQubits = 4;//about 5 minutes
            ModularSquMontgomeryFormExhaustiveTestHelper (ModularSquMontgomeryFormWindowedGeneric, nQubits);
        }
    }

    ///////////////// MODULAR SQUARING AND ADDING IN MONTGOMERY FORM /////////////////
    ///
    /// # Summary
    /// Squares an integer modulo a classical
    /// modulus, using Montgomery mulitplication.
    /// Requires n + 2 clean ancilla, which are returned 
    /// dirty.
    ///
    /// # Inputs
    /// ## xs
    /// The register to be squared.
    /// ## ancillas
    /// Clean ancillas that will be returned dirty. 
    /// ## blankOutputs
    /// A register input with all zeros, which will contain
    /// the intermediate result before uncomputing.
    ///
    /// # Operations
    /// This can test: 
    ///		* ModularSquMontgomeryFormOpen
    operation ModularSquMontgomeryFormOpenTestHelper(
        Squarer: ( (MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        input : BigInt, 
        modulus : BigInt, 
        nQubits : Int, 
        nAncillas : Int 
    ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits + nAncillas]){
                mutable actual = 0L;
                mutable result  = 0L;
                mutable ancilla = 0L;
                let ancillas = register[2 * nQubits .. 2 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable inputMMI = CreateBigIntInMontgomeryForm(modulus, input, LittleEndian(register[0..nQubits - 1]));
                mutable resultMMI = MontModInt(modulus, LittleEndian(register[1 * nQubits .. 2 * nQubits - 1]));
                
                // Run test
                Squarer(inputMMI, ancillas, resultMMI);

                // Compute expected classical result
                let square = (input * input) % modulus;

                // Check results
                set actual = MeasureMontgomeryInteger(inputMMI);
                Fact(actual == input, $"Input 1: Expected {input}, got {actual}");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == square, $"Result: Expected {square}, got {result}");

                // Rewrite results to measured qubit registers
                EncodeBigIntInMontgomeryForm(input, inputMMI);
                EncodeBigIntInMontgomeryForm(square, resultMMI);

                // Uncompute test
                (Adjoint Squarer)(inputMMI, ancillas, resultMMI);

                // Check results
                set actual = MeasureMontgomeryInteger(inputMMI);
                Fact(actual == input, $"Uncomputed: Input 1: Expected {input}, got {actual}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureMontgomeryInteger(resultMMI);
                Fact(result == 0L, $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeBigIntInMontgomeryForm(input, inputMMI);

                        // Run test
                        (Controlled Squarer)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 0: Input 1: Expected {input}, got {actual}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Result: Expected 0, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(input, inputMMI);

                        // Uncompute test
                        (Controlled Adjoint Squarer)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 0: Uncomputed: Input 1: Expected {input}, got {actual}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeBigIntInMontgomeryForm(input, inputMMI);

                        // Run test
                        (Controlled Squarer)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 1: Input 1: Expected {input}, got {actual}");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == square, $"Control 1: Result: Expected {square}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeBigIntInMontgomeryForm(input, inputMMI);
                        EncodeBigIntInMontgomeryForm(square, resultMMI);

                        // Uncompute test
                        (Controlled Adjoint Squarer)(controls, (inputMMI, ancillas, resultMMI));

                        // Check results
                        set actual = MeasureMontgomeryInteger(inputMMI);
                        Fact(actual == input, $"Control 1: Uncomputed: Input 1: Expected {input}, got {actual}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureMontgomeryInteger(resultMMI);
                        Fact(result == 0L, $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation ModularSquMontgomeryFormOpenExhaustiveTestHelper ( 
        ModularSquarer : ( (MontModInt, Qubit[], MontModInt) => Unit is Ctl + Adj), 
        nQubits : Int, 
        nAncillas : Int 
    ) : Unit {
        body (...) {
            for (modulus in 2^(nQubits - 1) + 1 ..2.. 2^nQubits - 1) {
                for( integer in 0 .. modulus - 1 ) {
                    ModularSquMontgomeryFormOpenTestHelper(ModularSquarer, IntAsBigInt(integer), IntAsBigInt(modulus), nQubits, nAncillas);
                }
            }
        }
    }

    operation ModularSquMontgomeryFormOpenTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 15L;
            let integer = 13L; 
            let summand = 4L;
            let (nAncillas, _) = AncillaCountModularSquMontgomeryForm(nQubits);
            ModularSquMontgomeryFormOpenTestHelper(ModularSquMontgomeryFormOpen, integer, modulus, nQubits, nAncillas);
        }
    }

    operation ModularSquMontgomeryFormOpenExhaustiveTest () : Unit {
        body (...) {
            let nQubits = 4;
           // let nQubits = 5;//about 5 minutes
           let (nAncillas, _) = AncillaCountModularSquMontgomeryForm(nQubits);
            ModularSquMontgomeryFormOpenExhaustiveTestHelper (ModularSquMontgomeryFormOpen, nQubits, nAncillas);
        }
    }

}
