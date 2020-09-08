// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Tests.Fp2Arithmetic {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;

    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Fp2Arithmetic;

    ///////////////// Fp2 ADDITION /////////////////
    ///
    /// # Summary
    /// Computes the sum of two quantum elements of $F_{p^2}$ in place. 
    /// The inputs are represented as (a+bi) and (c+di), and the output
    /// is ((a+c)+(b+d)i)
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register containing the first summand.
    /// ## cds
    /// Qubit register containing the second summand, which will be overwritten
    /// with the result.
    /// 
    /// # Operations
    /// This can test:
    ///		* AddFp2ElementMontgomeryForm
     operation Fp2AddTestHelper( Adder:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl), summand1 : Fp2ElementClassical, summand2 : Fp2ElementClassical, nQubits : Int ) : Unit {
       // Bookkeeping and qubit allocation
       using (register = Qubit[4 * nQubits]) {
            // Write to qubit registers
            mutable summand1Q = CreateFp2MontModInt(summand1,register[0..2 * nQubits-1]);
            mutable summand2Q = CreateFp2MontModInt(summand2,register[2 * nQubits..4 * nQubits-1]);

            //Run tests
            Adder(summand1Q, summand2Q);
 
            //Compute expected classical result
            let expected = AddFp2ElementClassical(summand1,summand2);

            // Check results
            mutable actual1 = MeasureFp2MontModInt(summand1Q);
            Fact((summand1::real == actual1::real) and (summand1::imag == actual1::imag), $"Input: Expected {summand1}, got {actual1}");
            mutable result = MeasureFp2MontModInt(summand2Q);
            Fact((expected::real == result::real) and (expected::imag == result::imag), $"Output: Expected {expected}, got {result}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    //Write to qubit registers
                    set summand1Q = CreateFp2MontModInt(summand1,register[0..2 * nQubits-1]);
                    set summand2Q = CreateFp2MontModInt(summand2,register[2 * nQubits..4 * nQubits-1]);

                    // controls are |0>, no addition is computed
                    // Run test
                    (Controlled Adder) (controls, (summand1Q,summand2Q));

                    //Check results
                    set actual1 = MeasureFp2MontModInt(summand1Q);
                    Fact((summand1::real == actual1::real) and (summand1::imag == actual1::imag), $"Control 0: Input: Expected {summand1}, got {actual1}");
                    set result = MeasureFp2MontModInt(summand2Q);
                    Fact((summand2::real == result::real) and (summand2::imag == result::imag), $"Control 0: Output: Expected {summand2}, got {result}");

                    // Write to qubit registers
                    set summand1Q = CreateFp2MontModInt(summand1,register[0..2 * nQubits-1]);
                    set summand2Q = CreateFp2MontModInt(summand2,register[2 * nQubits..4 * nQubits-1]);

                    // now controls are set to |1>, addition is computed
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Adder) (controls, (summand1Q, summand2Q));

                    // Check results
                    set actual1 = MeasureFp2MontModInt(summand1Q);
                    Fact((summand1::real == actual1::real) and (summand1::imag == actual1::imag), $"Control 1: Input: Expected {summand1}, got {actual1}");
                    set result = MeasureFp2MontModInt(summand2Q);
                    Fact((expected::real == result::real) and (expected::imag == result::imag), $"Control 1: Output: Expected {expected}, got {result}");
                   
                    ResetAll(controls);
                }
            }
        }
    }

    operation Fp2AddRandomTestHelper( Adder:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl), nQubits:Int, nTests:Int):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2AddTestHelper( Adder, xFp2, yFp2, nQubits );
        }
    }
    operation Fp2AddRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2AddRandomTestHelper(AddFp2ElementMontgomeryForm,nQubits,nTests);
    }

    ///////////////// Fp2 MULTIPLICATION /////////////////
    ///
    /// # Summary
    /// Computes the product of two quantum elements of $F_{p^2}$, adding
    /// the result to a third element.
    /// The inputs are represented as (a+bi), (c+di), and (e+fi), and the output
    /// is (e+ac-bd)+(f+ad+bc)i.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register containing the first element, a+bi.
    /// ## cds
    /// Qubit register containing the second element, c+di.
    /// ## outputs
    /// Qubit register containing e+fi which will be added to the product.
    ///
    /// # Operations
    /// This can test:
    ///		* MulAndAddFp2ElementMontgomeryForm
     operation Fp2MultiplyTestHelper( Multiplier:((Fp2MontModInt,Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl), multiplicand1 : Fp2ElementClassical, 
            multiplicand2 : Fp2ElementClassical, summand:Fp2ElementClassical, nQubits : Int ) : Unit {
        using (register = Qubit[6 * nQubits]) {
            // Write to qubit register and create necessary variables
            mutable multiplicand1Q = CreateFp2MontModInt(multiplicand1,register[0..2 * nQubits-1]);
            mutable multiplicand2Q = CreateFp2MontModInt(multiplicand2,register[2 * nQubits..4 * nQubits-1]);
            mutable outputQ = CreateFp2MontModInt(summand,register[4 * nQubits..6 * nQubits-1]);

            // Run test
            Multiplier(multiplicand1Q, multiplicand2Q,outputQ);
 
            // Compute expected classical result
            let product = MultiplyFp2ElementClassical(multiplicand1,multiplicand2);
            let expected = AddFp2ElementClassical(product,summand);

            // Check results
            mutable actual1 = MeasureFp2MontModInt(multiplicand1Q);
            Fact((multiplicand1::real == actual1::real) and (multiplicand1::imag == actual1::imag), $"Input: Expected {multiplicand1}, got {actual1}");
            mutable actual2 = MeasureFp2MontModInt(multiplicand2Q);
            Fact((multiplicand2::real == actual2::real) and (multiplicand2::imag == actual2::imag), $"Input: Expected {multiplicand2}, got {actual2}");
            mutable result = MeasureFp2MontModInt(outputQ);
            Fact((expected::real == result::real) and (expected::imag == result::imag), $"Output: Expected {expected}, got {result}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    set multiplicand1Q = CreateFp2MontModInt(multiplicand1,register[0..2 * nQubits-1]);
                    set multiplicand2Q = CreateFp2MontModInt(multiplicand2,register[2 * nQubits..4 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[4 * nQubits..6 * nQubits-1]);

                    // controls are |0>, no multiplication is computed
                    // Run test
                    (Controlled Multiplier) (controls, (multiplicand1Q, multiplicand2Q,outputQ));

                    // Check results
                    set actual1 = MeasureFp2MontModInt(multiplicand1Q);
                    Fact((multiplicand1::real == actual1::real) and (multiplicand1::imag == actual1::imag), $"Control 0: Input: Expected {multiplicand1}, got {actual1}");
                    set actual2 = MeasureFp2MontModInt(multiplicand2Q);
                    Fact((multiplicand2::real == actual2::real) and (multiplicand2::imag == actual2::imag), $"Control 0: Input: Expected {multiplicand2}, got {actual2}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((summand::real == result::real) and (summand::imag == result::imag), $"Control 0: Output: Expected {summand}, got {result}");

                    // Write to qubit registers
                    set multiplicand1Q = CreateFp2MontModInt(multiplicand1,register[0..2 * nQubits-1]);
                    set multiplicand2Q = CreateFp2MontModInt(multiplicand2,register[2 * nQubits..4 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[4 * nQubits..6 * nQubits-1]);

                    // now controls are set to |1>, multiplication is computed
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Multiplier) (controls, (multiplicand1Q, multiplicand2Q,outputQ));

                    // Check results
                    set actual1 = MeasureFp2MontModInt(multiplicand1Q);
                    Fact((multiplicand1::real == actual1::real) and (multiplicand1::imag == actual1::imag), $"Control 1: Input: Expected {multiplicand1}, got {actual1}");
                    set actual2 = MeasureFp2MontModInt(multiplicand2Q);
                    Fact((multiplicand2::real == actual2::real) and (multiplicand2::imag == actual2::imag), $"Control 1: Input: Expected {multiplicand2}, got {actual2}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((expected::real == result::real) and (expected::imag == result::imag), $"Control 1: Output: Expected {expected}, got {result}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation Fp2MultiplyAndXorRandomTestHelper( Multiplier:((Fp2MontModInt,Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl),nQubits:Int,nTests:Int):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L,0L);
            Fp2MultiplyTestHelper( Multiplier, xFp2, yFp2, zeroFp2,nQubits );
        }
    }
    operation Fp2MultiplyAndXorRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2MultiplyAndXorRandomTestHelper(MulAndXorFp2ElementMontgomeryForm,nQubits,nTests);
    }
    operation Fp2MultiplyAndAddRandomTestHelper( Multiplier:((Fp2MontModInt,Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl),nQubits:Int,nTests:Int):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            let zFp2 = RandomFp2ElementClassical(modulus);
            Fp2MultiplyTestHelper( Multiplier, xFp2, yFp2, zFp2,nQubits );
        }
    }
    operation Fp2MultiplyAndAddRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2MultiplyAndAddRandomTestHelper(MulAndAddFp2ElementMontgomeryForm,nQubits,nTests);
    }

    ///////////////// OPEN Fp2 MULTIPLICATION /////////////////
    ///
    /// # Summary
    /// Multiplies two elements of $F_{p^2}$ encoded in qubit registers,
    /// taking clean ancilla and returning them dirty.
    ///
    /// # Description
    /// The inputs are represented as (a+bi), (c+di), and (e+fi), and the output
    /// is (e+ac-bd)+(f+ad+bc)i.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register containing the first element, a+bi.
    /// ## cds
    /// Qubit register containing the second element, c+di.
    /// ## ancillas
    /// Register of clean ancillas.
    /// ## blankOutputs
    /// Blank qubit register which will contain the product.
    /// 
    /// # Operations
    /// This can test:
    ///		* MulFp2ElementMontgomeryFormOpen
    operation Fp2MultiplyOpenTestHelper(
        Fp2Multiplier: ( (Fp2MontModInt, Fp2MontModInt, Qubit[], Fp2MontModInt) => Unit is Ctl + Adj), 
        multiplier1 : Fp2ElementClassical,
        multiplier2 : Fp2ElementClassical, 
        nQubits : Int,
        nAncilla : Int 
        ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[6 * nQubits + nAncilla]){
                let modulus = multiplier1::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                mutable actual1 = zeroFp2;
                mutable actual2 = zeroFp2;
                mutable result = zeroFp2;
                mutable ancilla = 0L;
                let ancillas = register[6 * nQubits .. 6 * nQubits + nAncilla - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable multiplier1Q = CreateFp2MontModInt(multiplier1, register[0..2 * nQubits-1]);
                mutable multiplier2Q = CreateFp2MontModInt(multiplier2, register[2 * nQubits..4 * nQubits-1]);
                mutable resultQ = CreateFp2MontModInt(zeroFp2, register[4 * nQubits..6 * nQubits-1]);
                
                // Run test
                Fp2Multiplier(multiplier1Q, multiplier2Q, ancillas, resultQ);

                // Compute expected classical result
                let prod = MultiplyFp2ElementClassical(multiplier1, multiplier2);

                // Check results
                set actual1 = MeasureFp2MontModInt(multiplier1Q);
                Fact(IsEqualFp2Element(actual1, multiplier1), $"Input 1: Expected {multiplier1}, got {actual1}");
                set actual2 = MeasureFp2MontModInt(multiplier2Q);
                Fact(IsEqualFp2Element(actual2, multiplier2), $"Input 2: Expected {multiplier2}, got {actual2}");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, prod), $"Result: Expected {prod}, got {result}");

                // Rewrite results to measured qubit registers
                EncodeFp2MontModInt(multiplier1, multiplier1Q);
                EncodeFp2MontModInt(multiplier2, multiplier2Q);
                EncodeFp2MontModInt(prod, resultQ);

                // Un-compute test
                (Adjoint Fp2Multiplier)(multiplier1Q, multiplier2Q, ancillas, resultQ);

                // Check results
                set actual1 = MeasureFp2MontModInt(multiplier1Q);
                Fact(IsEqualFp2Element(actual1, multiplier1), $"Uncomputed: Input 1: Expected {multiplier1}, got {actual1}");
                set actual2 = MeasureFp2MontModInt(multiplier2Q);
                Fact(IsEqualFp2Element(actual2, multiplier2), $"Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, zeroFp2), $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        //Write to qubit registers
                        EncodeFp2MontModInt(multiplier1, multiplier1Q);
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);

                        // Run test
                        (Controlled Fp2Multiplier)(controls, (multiplier1Q, multiplier2Q, ancillas, resultQ));

                        //Check results
                        set actual1 = MeasureFp2MontModInt(multiplier1Q);
                        Fact(IsEqualFp2Element(actual1, multiplier1), $"Control 0: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 0: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Result: Expected 0, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(multiplier1, multiplier1Q);
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);

                        // Uncompute test
                        (Controlled Adjoint Fp2Multiplier)(controls, (multiplier1Q, multiplier2Q, ancillas, resultQ));

                        //Check results
                        set actual1 = MeasureFp2MontModInt(multiplier1Q);
                        Fact(IsEqualFp2Element(actual1, multiplier1), $"Control 0: Uncomputed: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 0: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit registers
                        EncodeFp2MontModInt(multiplier1, multiplier1Q);
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);

                        // Run test
                        (Controlled Fp2Multiplier)(controls, (multiplier1Q, multiplier2Q, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(multiplier1Q);
                        Fact(IsEqualFp2Element(actual1, multiplier1), $"Control 1: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 1: Input 2: Expected {multiplier2}, got {actual2}");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, prod), $"Control 1: Result: Expected {prod}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(multiplier1, multiplier1Q);
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);
                        EncodeFp2MontModInt(prod, resultQ);

                        // Uncompute test
                        (Controlled Adjoint Fp2Multiplier)(controls, (multiplier1Q, multiplier2Q, ancillas, resultQ));

                        //Check results
                        set actual1 = MeasureFp2MontModInt(multiplier1Q);
                        Fact(IsEqualFp2Element(actual1, multiplier1), $"Control 1: Uncomputed: Input 1: Expected {multiplier1}, got {actual1}");
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 1: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation Fp2MultiplyOpenRandomTestHelper(
        Multiplier:((Fp2MontModInt, Fp2MontModInt, Qubit[], Fp2MontModInt)=> Unit is Ctl + Adj),
        nQubits:Int, 
        nAncilla : Int, 
        nTests:Int
        ):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2MultiplyOpenTestHelper( Multiplier, xFp2, yFp2, nQubits, nAncilla );
        }
    }
    operation Fp2MultiplyOpenRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        let (nAncilla, _) = 	AncillaCountFp2MulMontgomeryForm (nQubits);
        Fp2MultiplyOpenRandomTestHelper(MulFp2ElementMontgomeryFormOpen, nQubits, nAncilla, nTests);
    }

    ///////////////// Fp2 MULTIPLICATION BY A CONSTANT /////////////////
    ///
    /// # Summary
    /// Multiplies two elements of $F_{p^2}$, one classical
    /// and the other encoded in a qubit regiter,
    /// and adds the result to an output qubit register.
    ///
    ///
    /// # Inputs
    /// The inputs are represented as (a+bi), (c+di), and (e+fi), and the output
    /// is (e+ac-bd)+(f+ad+bc)i.
    ///
    /// # Inputs
    /// ## constant
    /// Classical register containing c+di.
    /// ## cds
    /// Qubit register containing a+bi.
    /// ## outputs
    /// Qubit register containing e+fi and will contain the output.
    ///
    /// # Operations
    /// This can test:
    ///		* MulByConstantAndAddFp2MontgomeryFormGeneric
     operation Fp2MultiplyConstantTestHelper( Multiplier:((Fp2ElementClassical, Fp2MontModInt, Fp2MontModInt)=> Unit is Ctl), 
        multiplicand1 : Fp2ElementClassical, 
        multiplicand2 : Fp2ElementClassical, 
        summand:Fp2ElementClassical, 
        nQubits : Int ) : Unit {
        using (register = Qubit[4 * nQubits]) {
            // Write to qubit registers and create qubit variables
            mutable multiplicand2Q = CreateFp2MontModInt(multiplicand2,register[0 * nQubits..2 * nQubits-1]);
            mutable outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

            // Run test
            Multiplier(multiplicand1, multiplicand2Q,outputQ);
 
            // Compute classical expected result
            let product = MultiplyFp2ElementClassical(multiplicand1,multiplicand2);
            let expected = AddFp2ElementClassical(product,summand);

            // Check results
            mutable actual2 = MeasureFp2MontModInt(multiplicand2Q);
            Fact((multiplicand2::real == actual2::real) and (multiplicand2::imag == actual2::imag), $"Input: Expected {multiplicand2}, got {actual2}");
            mutable result = MeasureFp2MontModInt(outputQ);
            Fact((expected::real == result::real) and (expected::imag == result::imag), $"Output: Expected {expected}, got {result}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    //Write to qubit registers
                    EncodeFp2MontModInt(multiplicand2, multiplicand2Q);
                    EncodeFp2MontModInt(summand, outputQ);

                    // controls are |0>, no multiplication is computed
                    // Run test
                    (Controlled Multiplier) (controls, (multiplicand1, multiplicand2Q,outputQ));

                    // Check results
                    set actual2 = MeasureFp2MontModInt(multiplicand2Q);
                    Fact((multiplicand2::real == actual2::real) and (multiplicand2::imag == actual2::imag), $"Control 0: Input: Expected {multiplicand2}, got {actual2}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((summand::real == result::real) and (summand::imag == result::imag), $"Control 0: Output: Expected {summand}, got {result}");

                    // Write to qubit registers
                    EncodeFp2MontModInt(multiplicand2, multiplicand2Q);
                    EncodeFp2MontModInt(summand, outputQ);

                    // now controls are set to |1>, multiplication is computed
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Multiplier) (controls, (multiplicand1, multiplicand2Q,outputQ));

                    // Check results
                    set actual2 = MeasureFp2MontModInt(multiplicand2Q);
                    Fact((multiplicand2::real == actual2::real) and (multiplicand2::imag == actual2::imag), $"Control 1: Input: Expected {multiplicand2}, got {actual2}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((expected::real == result::real) and (expected::imag == result::imag), $"Control 1: Output: Expected {expected}, got {result}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation Fp2MultiplyConstantAndAddRandomTestHelper( 
        Multiplier:((Fp2ElementClassical, Fp2MontModInt, Fp2MontModInt)=> Unit is Ctl),
        nQubits:Int,
        nTests:Int):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            let zFp2 = RandomFp2ElementClassical(modulus);
            Fp2MultiplyConstantTestHelper( Multiplier, xFp2, yFp2, zFp2,nQubits );
        }
    }
    operation Fp2MultiplyConstantAndAddRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2MultiplyConstantAndAddRandomTestHelper(MulByConstantAndAddFp2MontgomeryFormGeneric,nQubits,nTests);
    }

    ///////////////// OPEN Fp2 MULTIPLICATION BY A CONSTANT /////////////////
    ///
    /// # Summary
    /// Multiplies two elements of $F_{p^2}$, one classical
    /// and the other encoded in a qubit regiter,
    /// taking clean ancillas and returning them dirty.
    ///
    ///
    /// # Inputs
    /// The inputs are represented as (a+bi), (c+di), and (e+fi), and the output
    /// is (e+ac-bd)+(f+ad+bc)i.
    ///
    /// # Inputs
    /// ## constant
    /// Classical element c+di
    /// ## cds
    /// Qubit register containing the second element, c+di.
    /// ## ancillas
    /// Register of clean ancillas.
    /// ## blankOutputs
    /// Blank qubit register which will contain the product.
    ///
    /// # Operations
    /// This can test:
    ///		* MulByConstantFp2MontgomeryFormOpen
    operation Fp2MulConstantMontgomeryFormOpenTestHelper(
        Fp2Multiplier: ( (Fp2ElementClassical, Fp2MontModInt, Qubit[], Fp2MontModInt) => Unit is Ctl + Adj), 
        multiplier1 : Fp2ElementClassical,
        multiplier2 : Fp2ElementClassical, 
        nQubits : Int,
        nAncilla : Int 
        ) : Unit {
        body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[4 * nQubits + nAncilla]){
                let ancillas = register[6 * nQubits .. 6 * nQubits + nAncilla - 1];
                let ancillaLE = LittleEndian(ancillas);
                mutable ancilla = 0L;
                let modulus = multiplier1::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                mutable actual2 = zeroFp2;
                mutable result  = zeroFp2;
            
                // Write to qubit registers
                mutable multiplier2Q = CreateFp2MontModInt(multiplier2, register[0..2 * nQubits - 1]);
                mutable resultQ = CreateFp2MontModInt(zeroFp2, register[2 * nQubits .. 4 * nQubits - 1]);
                
                // Run test
                Fp2Multiplier(multiplier1, multiplier2Q, ancillas, resultQ);

                // Compute classical expected result
                let prod = MultiplyFp2ElementClassical(multiplier1, multiplier2);

                // Check results
                set actual2 = MeasureFp2MontModInt(multiplier2Q);
                Fact(IsEqualFp2Element(actual2, multiplier2), $"Input 1: Expected {multiplier2}, got {actual2}");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, prod), $"Result: Expected {prod}, got {result}");

                // Rewrite results to measured qubit registers
                EncodeFp2MontModInt(multiplier2, multiplier2Q);
                EncodeFp2MontModInt(prod, resultQ);

                // Uncompute test
                (Adjoint Fp2Multiplier)(multiplier1, multiplier2Q, ancillas, resultQ);

                //Check results
                set actual2 = MeasureFp2MontModInt(multiplier2Q);
                Fact(IsEqualFp2Element(actual2, multiplier2), $"Uncomputed: Input 1: Expected {multiplier2}, got {actual2}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, zeroFp2), $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);

                        // Run test
                        (Controlled Fp2Multiplier)(controls, (multiplier1, multiplier2Q, ancillas, resultQ));

                        // Check results
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 0: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Result: Expected 0, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);

                        // Uncompute test
                        (Controlled Adjoint Fp2Multiplier)(controls, (multiplier1, multiplier2Q, ancillas, resultQ));

                        // Check results
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 0: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);

                        // Run test
                        (Controlled Fp2Multiplier)(controls, (multiplier1, multiplier2Q, ancillas, resultQ));

                        // Check results
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2 , multiplier2), $"Control 1: Input 2: Expected {multiplier2}, got {actual2}");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, prod), $"Control 1: Result: Expected {prod}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(multiplier2, multiplier2Q);
                        EncodeFp2MontModInt(prod, resultQ);

                        // Run test
                        (Controlled Adjoint Fp2Multiplier)(controls, (multiplier1, multiplier2Q, ancillas, resultQ));

                        // Check results
                        set actual2 = MeasureFp2MontModInt(multiplier2Q);
                        Fact(IsEqualFp2Element(actual2, multiplier2), $"Control 1: Uncomputed: Input 2: Expected {multiplier2}, got {actual2}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation Fp2MultiplyConstantOpenRandomTestHelper(
        Multiplier:((Fp2ElementClassical, Fp2MontModInt, Qubit[], Fp2MontModInt)=> Unit is Ctl + Adj),
        nQubits:Int, 
        nAncilla : Int, 
        nTests:Int
        ):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2MulConstantMontgomeryFormOpenTestHelper( Multiplier, xFp2, yFp2, nQubits, nAncilla );
        }
    }
    operation Fp2MultiplyConstantOpenRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        let (nAncilla, _) = 	AncillaCountFp2MulConstantMontgomeryForm (nQubits);
        Fp2MultiplyConstantOpenRandomTestHelper(MulByConstantFp2MontgomeryFormOpen, nQubits, nAncilla, nTests);
    }

    ///////////////// Fp2 SQUARING /////////////////
    ///
    /// # Summary
    /// Takes an element (a+bi) of $F_{p^2}$ encoded in 
    /// Montgomer form in qubit registers, and computes
    /// the square ((a^2-b^2)+2abi), and adds this result
    /// into an output register.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register which will be squared
    /// ## absquareds
    /// Qubit register which will be added with the output
    ///
    /// # Operations
    /// This can test:
    ///		* SquAndAddFp2ElementMontgomeryForm
     operation Fp2SquareTestHelper( Squarer:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl), input : Fp2ElementClassical, 
             summand:Fp2ElementClassical, nQubits : Int ) : Unit {
        using (register = Qubit[4 * nQubits]) {
            // Write to qubit registers and create variables
            mutable baseQ = CreateFp2MontModInt(input,register[0..2 * nQubits-1]);
            mutable outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

            // Run test
            Squarer(baseQ,outputQ);
 
            // Compute classical expected result
            let product = SquareFp2ElementClassical(input);
            let expected = AddFp2ElementClassical(product,summand);

            // Check results
            mutable actual1 = MeasureFp2MontModInt(baseQ);
            Fact((input::real == actual1::real) and (input::imag == actual1::imag), $"Input: Expected {input}, got {actual1}");
            mutable result = MeasureFp2MontModInt(outputQ);
            Fact((expected::real == result::real) and (expected::imag == result::imag), $"Output: Expected {expected}, got {result}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    set baseQ = CreateFp2MontModInt(input,register[0..2 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

                    // controls are |0>, no multiplication is computed
                    // Run test
                    (Controlled Squarer) (controls, (baseQ,outputQ));

                    //Check results
                    set actual1 = MeasureFp2MontModInt(baseQ);
                    Fact((input::real == actual1::real) and (input::imag == actual1::imag), $"Control 0: Input: Expected {input}, got {actual1}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((summand::real == result::real) and (summand::imag == result::imag), $"Control 0: Output: Expected {summand}, got {result}");

                    // Write to qubit registers
                    set baseQ = CreateFp2MontModInt(input,register[0..2 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

                    // now controls are set to |1>, multiplication is computed
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Squarer) (controls, (baseQ,outputQ));

                    // Check results
                    set actual1 = MeasureFp2MontModInt(baseQ);
                    Fact((input::real == actual1::real) and (input::imag == actual1::imag), $"Control 1: Input: Expected {input}, got {actual1}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((expected::real == result::real) and (expected::imag == result::imag), $"Control 1: Output: Expected {expected}, got {result}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation Fp2SquareAndXorRandomTestHelper( Squarer:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl),nQubits:Int,nTests:Int):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L,0L);
            Fp2SquareTestHelper( Squarer, xFp2,zeroFp2,nQubits );
        }
    }
    operation Fp2SquareAndXorRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2SquareAndXorRandomTestHelper(SquAndXorFp2ElementMontgomeryForm,nQubits,nTests);
    }
    operation Fp2SquareAndAddRandomTestHelper( Squarer:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl),nQubits:Int,nTests:Int):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2SquareTestHelper( Squarer, xFp2, yFp2,nQubits );
        }
    }
    operation Fp2SquareAndAddRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2SquareAndAddRandomTestHelper(SquAndAddFp2ElementMontgomeryForm,nQubits,nTests);
    }

    ///////////////// OPEN Fp2 SQUARING /////////////////
    ///
    /// # Summary
    /// Takes an element (a+bi) of $F_{p^2}$ encoded in 
    /// Montgomery form in qubit registers, and computes
    /// the square ((a^2-b^2)+2abi) into an output register.
    /// Takes clean ancilla which it returns dirty.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register encoding $F_{p^2}$ element which will be squared
    /// ## ancillas
    /// Clean ancilla which are returned dirty.
    /// ## blankOutputs
    /// Empty qubit register which will contain the square.
    /// 
    /// # Operations
    /// This can test:
    ///		* SquFp2ElementMontgomeryFormOpen
    operation Fp2SquareOpenTestHelper(
        Fp2Squarer: ( (Fp2MontModInt, Qubit[], Fp2MontModInt) => Unit is Ctl + Adj), 
        input : Fp2ElementClassical,
        nQubits : Int,
        nAncilla : Int 
        ) : Unit {
        body (...) {
            using (register = Qubit[4 * nQubits + nAncilla]){
                // Bookkeeping and allocation
                let modulus = input::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                mutable actual1 = zeroFp2;
                mutable result = zeroFp2;
                mutable ancilla = 0L;
                let ancillas = register[4 * nQubits .. 4 * nQubits + nAncilla - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable inputQ = CreateFp2MontModInt(input, register[0..2 * nQubits-1]);
                mutable resultQ = CreateFp2MontModInt(zeroFp2, register[2 * nQubits..4 * nQubits-1]);
                
                // Run test
                Fp2Squarer(inputQ, ancillas, resultQ);

                // Compute classical expected result
                let prod = SquareFp2ElementClassical(input);

                // Check results
                set actual1 = MeasureFp2MontModInt(inputQ);
                Fact(IsEqualFp2Element(actual1, input), $"Input 1: Expected {input}, got {actual1}");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, prod), $"Result: Expected {prod}, got {result}");

                // Rewrite results to measured qubit registers
                EncodeFp2MontModInt(input, inputQ);
                EncodeFp2MontModInt(prod, resultQ);

                // Uncompute test
                (Adjoint Fp2Squarer)(inputQ, ancillas, resultQ);

                //Check results
                set actual1 = MeasureFp2MontModInt(inputQ);
                Fact(IsEqualFp2Element(actual1, input), $"Uncomputed: Input 1: Expected {input}, got {actual1}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, zeroFp2), $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeFp2MontModInt(input, inputQ);

                        // Run tests
                        (Controlled Fp2Squarer)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 0: Input 1: Expected {input}, got {actual1}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Result: Expected 0, got {result}");

                        // Write to qubit register
                        EncodeFp2MontModInt(input, inputQ);

                        // Uncompute test
                        (Controlled Adjoint Fp2Squarer)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 0: Uncomputed: Input 1: Expected {input}, got {actual1}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeFp2MontModInt(input, inputQ);

                        // Run test
                        (Controlled Fp2Squarer)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 1: Input 1: Expected {input}, got {actual1}");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, prod), $"Control 1: Result: Expected {prod}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(input, inputQ);
                        EncodeFp2MontModInt(prod, resultQ);

                        // Uncompute test
                        (Controlled Adjoint Fp2Squarer)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 1: Uncomputed: Input 1: Expected {input}, got {actual1}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation Fp2SquareOpenRandomTestHelper(
        Squarer:((Fp2MontModInt, Qubit[], Fp2MontModInt)=> Unit is Ctl + Adj),
        nQubits:Int, 
        nAncilla : Int, 
        nTests:Int
        ):Unit {
        for (roundnum in 0..nTests-1){
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2SquareOpenTestHelper( Squarer, xFp2, nQubits, nAncilla );
        }
    }
    operation Fp2SquareOpenRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        let (nAncilla, _) = 	AncillaCountFp2SquMontgomeryForm (nQubits);
        Fp2SquareOpenRandomTestHelper(SquFp2ElementMontgomeryFormOpen, nQubits, nAncilla, nTests);
    }

    ///////////////// Fp2 INVERSION /////////////////
    ///
    /// # Summary
    /// Inverts an element of $F_{p^2}$ encoded in Montgomery Form
    /// in a qubit register, and adds the result to a quantum output register.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register which is inverted.
    /// ## cds
    /// Qubit register to which the inverse will be added.
    ///
    /// # Operations
    /// This can test:
    ///		* InvertAndAddFp2ElementMontgomeryForm
    operation Fp2InverseTestHelper( Inverter:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl), input : Fp2ElementClassical, 
             summand:Fp2ElementClassical, nQubits : Int ) : Unit {
        using (register = Qubit[4 * nQubits]) {
            // Write to qubit registers and create variables
            mutable baseQ = CreateFp2MontModInt(input,register[0..2 * nQubits-1]);
            mutable outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

            // Run test
            Inverter(baseQ,outputQ);

            // Compute classical expected result
            mutable inverse = Fp2ElementClassical(input::modulus,0L,0L);
            if (not ((input::real^2 + input::imag^2) % input::modulus == 0L)){
                set inverse = InvertFp2ElementClassical(input);
            }
            let expected = AddFp2ElementClassical(inverse,summand);

            //Check results
            mutable actual1 = MeasureFp2MontModInt(baseQ);
            Fact((input::real == actual1::real) and (input::imag == actual1::imag), $"Input: Expected {input}, got {actual1}");
            mutable result = MeasureFp2MontModInt(outputQ);
            Fact((expected::real == result::real) and (expected::imag == result::imag), $"Output: Expected {expected}, got {result}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    set baseQ = CreateFp2MontModInt(input,register[0..2 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

                    // controls are |0>, no multiplication is computed
                    // Run test
                    (Controlled Inverter) (controls, (baseQ,outputQ));

                    // Check results
                    set actual1 = MeasureFp2MontModInt(baseQ);
                    Fact((input::real == actual1::real) and (input::imag == actual1::imag), $"Control 0: Input: Expected {input}, got {actual1}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((summand::real == result::real) and (summand::imag == result::imag), $"Control 0: Output: Expected {summand}, got {result}");

                    // Write to qubit registers
                    set baseQ = CreateFp2MontModInt(input,register[0..2 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[2 * nQubits..4 * nQubits-1]);

                    // now controls are set to |1>, multiplication is computed
                    ApplyToEach(X, controls);

                    // Run test
                     (Controlled Inverter) (controls, (baseQ,outputQ));

                     // Check results
                    set actual1 = MeasureFp2MontModInt(baseQ);
                    Fact((input::real == actual1::real) and (input::imag == actual1::imag), $"Control 1: Input: Expected {input}, got {actual1}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((expected::real == result::real) and (expected::imag == result::imag), $"Control 1: Output: Expected {expected}, got {result}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation Fp2InvertAndAddRandomTestHelper( Inverter:((Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl),nQubits:Int,nTests:Int):Unit {
        mutable idxTest = 0;
        repeat {
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomInvertibleFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2InverseTestHelper( Inverter, xFp2,yFp2,nQubits );
            set idxTest = idxTest + 1;
        } until (idxTest >= nTests);
    }

    operation Fp2InvertAndAddRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2InvertAndAddRandomTestHelper(InvertAndAddFp2ElementMontgomeryForm,nQubits,nTests);
    }

    ///////////////// OPEN Fp2 INVERSION /////////////////
    ///
    /// # Summary
    /// Inverts an element of $F_{p^2}$ encoded in Montgomery Form
    /// in a qubit register. Requires clean ancillas which are returned
    /// dirty. 
    ///
    /// # Description
    /// Given an input of a+bi, saves $\frac{a}{a^2+b^2}+\frac{-b}{a^2+b^2}i$
    /// into an output register which is initialized as all zeros.
    ///
    /// # Inputs
    /// ## abs
    /// Input qubit register to be inverted
    /// ## ancillas
    /// Clean ancillas which are returned dirty
    /// ## blankOutputs
    /// Output element initialized to zero.
    ///
    /// # Operations
    /// This can test:
    ///		* InvFp2ElementMontgomeryFormOpen
    operation Fp2InverseOpenTestHelper(
        Fp2Inverter: ( (Fp2MontModInt, Qubit[], Fp2MontModInt) => Unit is Ctl + Adj), 
        input : Fp2ElementClassical,
        nQubits : Int,
        nAncilla : Int 
        ) : Unit {
        body (...) {
            using (register = Qubit[4 * nQubits + nAncilla]){
                // Bookkeeping and qubit allocation
                let modulus = input::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                mutable actual1 = zeroFp2;
                mutable result = zeroFp2;
                mutable ancilla = 0L;
                let ancillas = register[4 * nQubits .. 4 * nQubits + nAncilla - 1];
                let ancillaLE = LittleEndian(ancillas);

                // Write to qubit registers
                mutable inputQ = CreateFp2MontModInt(input, register[0..2 * nQubits-1]);
                mutable resultQ = CreateFp2MontModInt(zeroFp2, register[2 * nQubits..4 * nQubits-1]);
                
                // Run test
                Fp2Inverter(inputQ, ancillas, resultQ);

                // Compute classical expected result
                mutable inverse = zeroFp2;
                if (not (input::real == 0L and input::imag == 0L)){
                    set inverse = InvertFp2ElementClassical(input);
                }

                //Check results
                set actual1 = MeasureFp2MontModInt(inputQ);
                Fact(IsEqualFp2Element(actual1, input), $"Input 1: Expected {input}, got {actual1}");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, inverse), $"Result: Expected {inverse}, got {result}");

                // Rewrite results to measure qubit registers
                EncodeFp2MontModInt(input, inputQ);
                EncodeFp2MontModInt(inverse, resultQ);

                // Uncompute test
                (Adjoint Fp2Inverter)(inputQ, ancillas, resultQ);

                //Check results
                set actual1 = MeasureFp2MontModInt(inputQ);
                Fact(IsEqualFp2Element(actual1, input), $"Uncomputed: Input 1: Expected {input}, got {actual1}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureFp2MontModInt(resultQ);
                Fact(IsEqualFp2Element(result, zeroFp2), $"Uncomputed: Result: Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeFp2MontModInt(input, inputQ);

                        // Run test
                        (Controlled Fp2Inverter)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 0: Input 1: Expected {input}, got {actual1}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Result: Expected 0, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(input, inputQ);

                        // Uncompute test
                        (Controlled Adjoint Fp2Inverter)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 0: Uncomputed: Input 1: Expected {input}, got {actual1}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Uncomputed: Result: Expected 0, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeFp2MontModInt(input, inputQ);

                        // Run test
                        (Controlled Fp2Inverter)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 1: Input 1: Expected {input}, got {actual1}");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, inverse), $"Control 1: Result: Expected {inverse}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeFp2MontModInt(input, inputQ);
                        EncodeFp2MontModInt(inverse, resultQ);

                        // Uncompute test
                        (Controlled Adjoint Fp2Inverter)(controls, (inputQ, ancillas, resultQ));

                        // Check results
                        set actual1 = MeasureFp2MontModInt(inputQ);
                        Fact(IsEqualFp2Element(actual1, input), $"Control 1: Uncomputed: Input 1: Expected {input}, got {actual1}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Uncomputed: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(resultQ);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 1: Uncomputed: Result: Expected 0, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }


    operation Fp2InverseOpenRandomTestHelper(
        Inverter:((Fp2MontModInt, Qubit[], Fp2MontModInt)=> Unit is Ctl + Adj),
        nQubits:Int, 
        nAncilla : Int, 
        nTests:Int
        ):Unit {
        mutable idxTest = 0;
        repeat {
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomInvertibleFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            Fp2InverseOpenTestHelper(Inverter, xFp2, nQubits, nAncilla);
            set idxTest = idxTest + 1;
        } until (idxTest >= nTests);
    }
    operation Fp2InverseOpenRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        let (nAncilla, _) = AncillaCountFp2InvMontgomeryForm (nQubits);
        Fp2InverseOpenRandomTestHelper(InvFp2ElementMontgomeryFormOpen, nQubits, nAncilla, nTests);
    }

    ///////////////// Fp2 DIVISION /////////////////
    ///
    /// # Summary
    /// Given three elements a+bi, c+di, e+fi of $F_{p^2}$ in qubit registers encoded
    /// in Montgomery form, adds $(c+di)(a+bi)^{-1}$ to the register containing e+fi.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register containing a+bi
    /// ## cds
    /// Fp2MontModInt containing c+di
    /// ## efs
    /// Fp2MontModInt containing e+fi
    ///
    /// # Operations
    /// This can test:
    ///		* DivideAndAddFp2ElementMontgomeryForm
     operation Fp2DivideTestHelper( Divider:((Fp2MontModInt,Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl), invertand : Fp2ElementClassical, 
            multiplicand : Fp2ElementClassical, summand:Fp2ElementClassical, nQubits : Int ) : Unit {
        using (register = Qubit[6 * nQubits]) {
            // Write to qubit registers and create variables
            mutable invertandQ = CreateFp2MontModInt(invertand,register[0..2 * nQubits-1]);
            mutable multiplicandQ = CreateFp2MontModInt(multiplicand,register[2 * nQubits..4 * nQubits-1]);
            mutable outputQ = CreateFp2MontModInt(summand,register[4 * nQubits..6 * nQubits-1]);

            // Run test
            Divider(invertandQ, multiplicandQ,outputQ);
 
            // Compute expected classical results
            mutable inverse = Fp2ElementClassical(invertand::modulus, 0L,0L);
            if (not (invertand::real==0L and invertand::imag==0L)){
                set inverse = InvertFp2ElementClassical(invertand);
            }
            let product = MultiplyFp2ElementClassical(multiplicand,inverse);
            let expected = AddFp2ElementClassical(product,summand);

            // Check results
            mutable actual1 = MeasureFp2MontModInt(invertandQ);
            Fact((invertand::real == actual1::real) and (invertand::imag == actual1::imag), $"Input: Expected {invertand}, got {actual1}");
            mutable actual2 = MeasureFp2MontModInt(multiplicandQ);
            Fact((multiplicand::real == actual2::real) and (multiplicand::imag == actual2::imag), $"Input: Expected {multiplicand}, got {actual2}");
            mutable result = MeasureFp2MontModInt(outputQ);
            Fact((expected::real == result::real) and (expected::imag == result::imag), $"Output: Expected {expected}, got {result}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    // Write to qubit registers
                    set invertandQ = CreateFp2MontModInt(invertand,register[0..2 * nQubits-1]);
                    set multiplicandQ = CreateFp2MontModInt(multiplicand,register[2 * nQubits..4 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[4 * nQubits..6 * nQubits-1]);

                    // controls are |0>, no multiplication is computed
                    // Run test
                    (Controlled Divider) (controls, (invertandQ, multiplicandQ,outputQ));

                    // Check results
                    set actual1 = MeasureFp2MontModInt(invertandQ);
                    Fact((invertand::real == actual1::real) and (invertand::imag == actual1::imag), $"Control 0: Input: Expected {invertand}, got {actual1}");
                    set actual2 = MeasureFp2MontModInt(multiplicandQ);
                    Fact((multiplicand::real == actual2::real) and (multiplicand::imag == actual2::imag), $"Control 0: Input: Expected {multiplicand}, got {actual2}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((summand::real == result::real) and (summand::imag == result::imag), $"Control 0: Output: Expected {summand}, got {result}");

                    // Write to qubit registers
                    set invertandQ = CreateFp2MontModInt(invertand,register[0..2 * nQubits-1]);
                    set multiplicandQ = CreateFp2MontModInt(multiplicand,register[2 * nQubits..4 * nQubits-1]);
                    set outputQ = CreateFp2MontModInt(summand,register[4 * nQubits..6 * nQubits-1]);

                    // Flip controls
                    ApplyToEach(X, controls);

                    // Run test
                    (Controlled Divider) (controls,(invertandQ, multiplicandQ,outputQ));

                    //Check results
                    set actual1 = MeasureFp2MontModInt(invertandQ);
                    Fact((invertand::real == actual1::real) and (invertand::imag == actual1::imag), $"Control 1: Input: Expected {invertand}, got {actual1}");
                    set actual2 = MeasureFp2MontModInt(multiplicandQ);
                    Fact((multiplicand::real == actual2::real) and (multiplicand::imag == actual2::imag), $"Control 1: Input: Expected {multiplicand}, got {actual2}");
                    set result = MeasureFp2MontModInt(outputQ);
                    Fact((expected::real == result::real) and (expected::imag == result::imag), $"Control 1: Output: Expected {expected}, got {result}");

                    ResetAll(controls);
                }
            }
        }
    }


    operation Fp2DivideAndAddRandomTestHelper( Divider:((Fp2MontModInt,Fp2MontModInt,Fp2MontModInt)=> Unit is Ctl),nQubits:Int,nTests:Int):Unit {
        mutable idxTest = 0;
        repeat {
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomInvertibleFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            let zFp2 = RandomFp2ElementClassical(modulus);
            Fp2DivideTestHelper( Divider, xFp2, yFp2, zFp2,nQubits );
            set idxTest = idxTest + 1;
        } until (idxTest >= nTests);
    }
    operation Fp2DivideAndAddRandomTest():Unit {
        let nQubits = 8;
        let nTests = 500;
        Fp2DivideAndAddRandomTestHelper(DivideAndAddFp2ElementMontgomeryForm,nQubits,nTests);
    }

}