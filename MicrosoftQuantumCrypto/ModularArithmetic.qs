// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.ModularArithmetic {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.ModularArithmetic.DebugHelpers;



    ////////////////////////////////////////////////////////////////////////////////////////////
    ///////                                                                             ////////
    ///////                          MODULAR ARITHMETIC                                 ////////
    ///////                                                                             ////////
    ////////////////////////////////////////////////////////////////////////////////////////////

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
    /// LittleEndian qubit register encoding the integer modulus.
    ///
    /// # Remarks
    /// This operation computes a modular multiplication where the two inputs
    /// and the modulus are encoded in qubit registers. The algorithm only works
    /// correctly for odd moduli since it relies on the operation ModularDbl.
    operation ModularMul (xs : LittleEndian, ys : LittleEndian, zs : LittleEndian, ms : LittleEndian) : Unit {
        body (...){
            ModularMulDblAdd(xs, ys, zs, ms);
        }
        adjoint controlled auto;
    }
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
    /// This operation computes a modular squaring where the input
    /// and the modulus are encoded in qubit registers. The algorithm only works
    /// correctly for odd moduli since it relies on the operation ModularDbl.
    operation ModularSqu (xs : LittleEndian, zs : LittleEndian, ms : LittleEndian) : Unit {
        body (...){
            ModularSquDblAdd(xs, zs, ms);
        }
        adjoint controlled auto;
    }

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
    /// Qubit register encoding the first integer $x$.
    operation ModularAddConstantConstantModulus (constant : BigInt, modulus : BigInt, xs : LittleEndian) : Unit {
        body (...) {
            ModularAddConstantConstantModulusSimple(constant, modulus, xs);
        }
        controlled adjoint auto;
    }

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
    /// # Remarks
    /// Since this operation relies on the operation ModularDblConstantModulus, 
    /// it only works correctly for odd moduli.
    operation ModularMulConstantModulus (modulus : BigInt, xs : LittleEndian, ys : LittleEndian, zs : LittleEndian) : Unit {
        body (...){
            ModularMulDblAddConstantModulus(modulus, xs, ys, zs);
        }
        adjoint controlled auto;
    }


    ////////// Unwrapped Functions ///////

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
    /// LittleEndian qubit register encoding the first integer x.
    ///
    /// # References    
    /// The algorithm for doubling modulo an odd number is sketched in Section 4.3.2 of
    /// - John Proos, Christof Zalka : "Shor's discrete logarithm quantum algorithm 
    ///   for elliptic curves", 2003.
    ///   https : //arxiv.org/abs/quant-ph/0301141/
    ///
    /// # Remarks
    /// This operation uses a simple approach of adding and comparing, exactly the same
    /// as a modular addition between two qubit registers.
    operation ModularAddConstantConstantModulusSimple(constant : BigInt, modulus : BigInt, xs : LittleEndian) : Unit {
        body (...){
            (Controlled ModularAddConstantConstantModulusSimple)(new Qubit[0], (constant%modulus, modulus, xs));
        }
        controlled (controls, ...){
            if (constant>=modulus){
                (Controlled ModularAddConstantConstantModulusSimple)(controls, (constant%modulus, modulus, xs));
            } else {
                using (carry = Qubit()){
                    (Controlled AddConstant)(controls, (constant, LittleEndian(xs!+[carry])));
                    (Controlled Adjoint AddConstant)(controls, (modulus, LittleEndian(xs!+[carry])));
                    (Controlled AddConstant)(controls+[carry], (modulus, xs));
                    (Controlled LessThanConstant)(controls, (constant, xs, carry));
                    (Controlled X)(controls, (carry));
                }
            }
        }
        controlled adjoint auto;
    }

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
    /// # References
    /// - The circuit is almost identical to the one in Fig. 4 of 
    ///   Vlatko Vedral, Adriano Barenco, Artur Ekert : Quantum Networks for  
    ///   Elementary Arithmetic Operations
    ///   http : //arxiv.org/abs/quant-ph/9511018v1.
    ///
    /// # Remarks
    /// This operation computes a modular addition where both inputs and the
    /// modulus are encoded in qubit registers. It uses two ancilla qubits. 
    /// The specified controlled operation makes use of symmetry and mutual 
    /// cancellation of operations to improve on the default implementation
    /// that adds a control to every operation. Additional NOT gates avoid 
    /// controlling of a not gate and save Toffoli gates if there are at
    /// least two control qubits.
    operation ModularAdd (xs : LittleEndian, ys : LittleEndian, ms : LittleEndian) : Unit
    {
        body (...) {
            let nQubits = Length(ms!);

            EqualityFactB(
                nQubits == Length(xs!), true, 
                "Input register xs must have the same number of qubits as the modulus." );
            EqualityFactB(
                nQubits == Length(ys!), true, 
                "Input register ys must have the same number of qubits as the modulus." );

            using ( carry = Qubit() ) {
                AddInteger(xs, ys, carry);
                (Adjoint AddInteger)(ms, ys, carry); 
                (Controlled AddIntegerNoCarry)([carry], (ms, ys));
                GreaterThanWrapper(xs, ys, carry);
                X(carry);
            }
        }
        adjoint controlled auto;
    }

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
    /// # Remarks
    /// This operation computes a modular negation where the input and the
    /// modulus are encoded in qubit registers.
    /// The specified controlled operation makes use of symmetry and mutual 
    /// cancellation of operations to improve on the default implementation
    /// that adds a control to every operation.
    /// This operation returns the modulus when given input 0.
    operation ModularNeg (xs : LittleEndian, ms : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularNeg) (new Qubit[0], (xs, ms));
        }
        adjoint auto;
        controlled ( controls, ... ) {
            let nQubits = Length(ms!);

            EqualityFactB(
                nQubits == Length(xs!), true, 
                "Input register xs must have the same number of qubits as the modulus." );
            using (isAllZeros = Qubit()){
                (Controlled X)(controls, isAllZeros);
                // Test if input is zero; it should remain zero
                (Controlled CheckIfAllZero)(controls, (xs!, isAllZeros));
                ApplyToEachWrapperCA(X, ms!); // (1)
                (Controlled AddIntegerNoCarry) ([isAllZeros], (ms, xs));
                // We negate every term of the input iff controls dictate
                (Controlled ApplyToEachWrapperCA)([isAllZeros], (X, xs!));
                ApplyToEachWrapperCA(X, ms!); // cancels with (1)
                (Controlled Adjoint CheckIfAllZero)(controls, (xs!, isAllZeros));// clears isAllZeros
                (Controlled X)(controls, isAllZeros);
            }
            
        }
        adjoint controlled auto;
    }

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
    /// # Remarks
    /// This operation computes a modular doubling where the input and the
    /// modulus are encoded in qubit registers. The algorithm only works
    /// correctly for odd moduli. For even modulus, the ancilla qubits
    /// will not necessarily be returned in the zero state.
    operation ModularDbl (xs : LittleEndian, ms : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularDbl) (new Qubit[0], (xs, ms));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(ms!);

            EqualityFactB(
                nQubits == Length(xs!), true, 
                "Input register xs must have the same number of qubits as the modulus." );

            using ((carry, control) = (Qubit(), Qubit())) {
                let xxs = LittleEndian( xs! + [carry] );

                (Controlled CyclicRotateRegister) (controls, xxs);
                (Adjoint AddInteger) (ms, xs, carry);
                CNOT(carry, control);
                (Controlled AddInteger) ([control], (ms, xs, carry));
                (Controlled CNOT) (controls, (xs![0], control));
                X(control);
            }
        }
        adjoint controlled auto;
    }

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
    /// # References
    /// The algorithm is described in Section 4.3.2 of
    /// - John Proos, Christof Zalka : "Shor's discrete logarithm quantum algorithm 
    ///   for elliptic curves", 2003.
    ///   https : //arxiv.org/abs/quant-ph/0301141
    ///
    /// # Remarks
    /// This operation computes a modular multiplication where the two inputs
    /// and the modulus are encoded in qubit registers. The algorithm only works
    /// correctly for odd moduli since it relies on the operation ModularDbl.
    operation ModularMulDblAdd (xs : LittleEndian, ys : LittleEndian, zs : LittleEndian, ms : LittleEndian) : Unit
    {
        body (...) {
            let nQubits = Length(ms!);

            EqualityFactB(
                nQubits == Length(xs!), true, 
                "Input register xs must have the same number of qubits as the modulus." );
            EqualityFactB(
                nQubits == Length(ys!), true, 
                "Input register ys must have the same number of qubits as the modulus." );
            EqualityFactB(
                nQubits == Length(zs!), true, 
                "Output register zs must have the same number of qubits as the modulus." );

            for (idx in nQubits-1 ..(-1).. 1) {
                (Controlled ModularAdd)([xs![idx]], (ys, zs, ms));
                ModularDbl(zs, ms);
            }
            (Controlled ModularAdd)([xs![0]], (ys, zs, ms));
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }

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
    /// # Remarks
    /// The algorithm is a specialization of ModularMulDblAdd and saves
    /// the qubits that would otherwise be required for the multiplier, 
    /// except for one qubit which it uses as an ancilla.
    ///
    /// This operation computes a modular squaring where the input
    /// and the modulus are encoded in qubit registers. The algorithm only works
    /// correctly for odd moduli since it relies on the operation ModularDbl.
    ///
    /// The controlled operation is specified manually because it saves the controls
    /// on the already controlled ModularAdd operation.
    operation ModularSquDblAdd (xs : LittleEndian, zs : LittleEndian, ms : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularSquDblAdd) (new Qubit[0], (xs, zs, ms));
        }
        adjoint auto;
        controlled ( controls, ... ) {
            let nQubits = Length(ms!);

            EqualityFactB(
                nQubits == Length(xs!), true, 
                "Input register xs must have the same number of qubits as the modulus." );
            EqualityFactB(
                nQubits == Length(zs!), true, 
                "Output register zs must have the same number of qubits as the modulus." );

            using (xsBitcopy = Qubit[1]) {
                for (idx in nQubits-1 ..(-1).. 1) {
                    (Controlled CNOT) (controls, (xs![idx], xsBitcopy[0]));
                    (Controlled ModularAdd)(xsBitcopy, (xs, zs, ms));
                    (Controlled CNOT) (controls, (xs![idx], xsBitcopy[0]));
                    (Controlled ModularDbl) (controls, (zs, ms));
                }
                (Controlled CNOT) (controls, (xs![0], xsBitcopy[0]));
                (Controlled ModularAdd)(xsBitcopy, (xs, zs, ms));
                (Controlled CNOT) (controls, (xs![0], xsBitcopy[0]));
            }
        }
        adjoint controlled auto;
    }

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
    /// # References
    /// - Yasuhiro Takahashi and Noboru Kunihiro : "A quantum circuit for Shor's factoring
    ///     algorithm using 2n + 2 qubits", Quantum Information & Computation 6 (2006)
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n+2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// This uses `AddInteger` and `GreaterThanWrapper` and will thus make the same trade-offs
    /// (i.e., low-depth or low-T).
    operation ModularAddConstantModulus (modulus : BigInt, xs : LittleEndian, ys : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularAddConstantModulus) (new Qubit[0], (modulus, xs, ys));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);

            EqualityFactB(
                nQubits == Length(ys!), true, 
                "Input register xs and ys must have the same number of qubits." );

            using (carry = Qubit[1]) {
                (Controlled AddInteger) (controls, (xs, ys, carry[0])); 
                (Adjoint AddConstant)(modulus, LittleEndian(ys! + carry));
                (Controlled AddConstant) (carry, (modulus, ys));
                (Controlled GreaterThanWrapper) (controls, (xs, ys, carry[0]));
                X(carry[0]);
            }
        }
        adjoint controlled auto;
    }


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
    /// # References
    /// The algorithm for doubling modulo an odd number is sketched in Section 4.3.2 of
    /// - John Proos, Christof Zalka : "Shor's discrete logarithm quantum algorithm 
    ///   for elliptic curves", 2003.
    ///   https : //arxiv.org/abs/quant-ph/0301141/
    ///
    /// # Remarks
    /// Like ModularDbl, this operation only works correctly for odd moduli. For even
    /// modulus, the ancilla qubits will not necessarily be returned in the zero state.
    /// The specified control operation makes use of symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation ModularDblConstantModulus (modulus : BigInt, xs : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularDblConstantModulus) (new Qubit[0], (modulus, xs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);

            EqualityFactB(
                modulus % 2L == 1L, true, 
                "ModularDbl requires modulus to be odd." );

            using ( ancillas = Qubit[1] ) {
                let carry = ancillas[0];
                let xxs = LittleEndian( xs! + [carry] );

                (Controlled CyclicRotateRegister) (controls, xxs);
                ApplyToEachWrapperCA(X, xxs!);
                AddConstant(modulus, xxs);
                ApplyToEachWrapperCA(X, xxs!);
                (Controlled AddConstant) ([carry], (modulus, xs));
                (Controlled CNOT) (controls, (xs![0], carry));
                X(carry);
            }
        }
        adjoint controlled auto;
    }

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
    /// # References    
    /// The algorithm for doubling modulo an odd number is sketched in Section 4.3.2 of
    /// - John Proos, Christof Zalka : "Shor's discrete logarithm quantum algorithm 
    ///   for elliptic curves", 2003.
    ///   https : //arxiv.org/abs/quant-ph/0301141/
    ///
    /// # Remarks
    /// The specified control operation makes use of symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation ModularAddConstantConstantModulusLowT (constant : BigInt, modulus : BigInt, xs : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularAddConstantConstantModulusLowT) (new Qubit[0], (constant, modulus, xs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            
            using (carry = Qubit[1]) {
                ApplyToEachWrapperCA(X, xs!);
                (Controlled ComputeCarry) (controls, (modulus - constant, xs, carry[0]));
                ApplyToEachWrapperCA(X, xs!);
                (Controlled AddConstant) (carry+controls, (constant, xs));
                (Controlled X) (controls, (carry[0]));
                ApplyToEachWrapperCA(X, xs!);
                (Controlled AddConstant) (carry+controls, (modulus - constant, xs));
                (Controlled ComputeCarry) (controls, (constant, xs, carry[0]));
                ApplyToEachWrapperCA(X, xs!);
            }
        }
        adjoint controlled auto;
    }



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
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y.
    /// ## zs
    /// Qubit register for the result. Must be
    /// in state $\ket{0}$ initially.
    ///
    /// # References
    /// An algorithm for multiplying two numbers modulo a constant is sketched in Section 4.3.2 of
    /// - John Proos, Christof Zalka : "Shor's discrete logarithm quantum algorithm 
    ///   for elliptic curves", 2003.
    ///   https : //arxiv.org/abs/quant-ph/0301141/
    ///
    /// # Remarks
    /// The operation uses the naive approach of modular doublings and controlled modular 
    /// additions as in the ModularMulDblAdd operation above. Since it relies on the operation
    /// ModularMulDblAddConstantModulus, it only works correctly for odd moduli.
    operation ModularMulDblAddConstantModulus (modulus : BigInt, xs : LittleEndian, ys : LittleEndian, zs : LittleEndian) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);

            EqualityFactB(
                nQubits == Length(ys!), true, 
                "Input register ys must have the same number of qubits as the modulus." );
            EqualityFactB(
                nQubits == Length(zs!), true, 
                "Output register zs must have the same number of qubits as the modulus." );

            for (idx in nQubits-1 ..(-1).. 1) {
                (Controlled ModularAddConstantModulus)([xs![idx]], (modulus, ys, zs));
                ModularDblConstantModulus(modulus, zs);
            }
            (Controlled ModularAddConstantModulus)([xs![0]], (modulus, ys, zs));
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }

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
    /// # References
    /// - The algorithm for modular squaring is described in Section 3.3 of 
    ///   Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n+2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// The specified control operation makes use of symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation ModularSquDblAddConstantModulus (modulus : BigInt, xs : LittleEndian, zs : LittleEndian) : Unit
    {
        body (...) {
            (Controlled ModularSquDblAddConstantModulus) (new Qubit[0], (modulus, xs, zs));
        }
        adjoint auto;
        controlled ( controls, ... ) {
            let nQubits = Length(xs!);
            EqualityFactB(
                nQubits == Length(zs!), true, 
                "Output register zs must have the same number of qubits as the modulus." );

            using (xsBitcopy = Qubit[1]) {
                for (idx in nQubits-1 ..(-1).. 1) {
                    (Controlled CNOT) (controls, (xs![idx], xsBitcopy[0]));
                    (Controlled ModularAddConstantModulus)(xsBitcopy, (modulus, xs, zs));
                    (Controlled CNOT) (controls, (xs![idx], xsBitcopy[0]));
                    (Controlled ModularDblConstantModulus) (controls, (modulus, zs));
                }
                (Controlled CNOT) (controls, (xs![0], xsBitcopy[0]));
                (Controlled ModularAddConstantModulus)(xsBitcopy, (modulus, xs, zs));
                (Controlled CNOT) (controls, (xs![0], xsBitcopy[0]));
            }
        }
        adjoint controlled auto;
    }

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
    /// # References
    /// - Steven A. Cuccaro, Thomas G. Draper, Samuel A. Kutin, David 
    ///   Petrie Moulton : "A new quantum ripple-carry addition circuit", 2004.
    ///   https : //arxiv.org/abs/quant-ph/0410184v1
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n+2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// Uses the trick that $x-y = (x'+y)'$, where ' denotes the one's complement.
    /// On input $(m, \ket{0\cdots 0})$, this outputs $\ket{0\cdots 0}$.
    operation ModularNegConstantModulus (modulus : BigInt, xs : LittleEndian) : Unit
    {
        body (...) {
            let negModulus = 2L^Length(xs!) - modulus - 1L;
            using (isAllZeros = Qubit()){
                //Test if the input is all-zeros
                CheckIfAllZero(xs!, isAllZeros);
                //If all-zeros, then put the modulus in xs
                (Controlled ApplyXorInPlaceL)([isAllZeros], (modulus, xs));
                //Adds m' to x
                AddConstant(negModulus, xs);
                // If x=0, then we m' + m = all ones
                CheckIfAllOnes(xs!, isAllZeros);
                //(Controlled X)(xs!, (isAllZeros));
                // Set to (m'+x)'
                ApplyToEachWrapperCA(X, xs!);
            }
        }
        controlled (controls, ...) {
            let negModulus = 2L^Length(xs!) - modulus - 1L;
            using (isAllZeros = Qubit()){
                (Controlled CheckIfAllZero)(controls, (xs!, isAllZeros));
                (Controlled ApplyXorInPlaceL)([isAllZeros], (modulus, xs));
                (Controlled AddConstant)(controls, (negModulus, xs));
                CheckIfAllOnes(controls+xs!, isAllZeros);
                //(Controlled X)(controls+xs!, (isAllZeros));
                (Controlled ApplyToEachWrapperCA)(controls, (X, xs!));
            }
        }
        adjoint auto;
        adjoint controlled auto;
    }


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
    /// # References
    /// - The circuit is Fig. 5 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///   except "classically curried" over "x"
    operation ModularMulByConstantConstantModulus(modulus : BigInt, constant : BigInt, xs : LittleEndian, ys : LittleEndian) : Unit{
        body (...) { 
            (Controlled ModularMulByConstantConstantModulus) (new Qubit[0], (modulus, constant, xs, ys));
        }
        controlled (controls, ... ){
            let constantAsArray = BigIntAsBoolArray(constant);
            for (idx in Length(constantAsArray)-1 ..(-1)..1){
                if (constantAsArray[idx]){
                    (Controlled ModularAddConstantModulus)(controls, (modulus, xs, ys));
                }
                (Controlled ModularDblConstantModulus)(controls, (modulus, ys));
            }
            if (constantAsArray[0]){
                (Controlled ModularAddConstantModulus)(controls, (modulus, xs, ys));
            }
        }
        adjoint controlled auto;
    }

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
    /// # Remarks
    /// The function calls MultiplyByConstantWithConstantModulus
    /// twice, once in Adjoint, using c and c^-1.
    operation ModularMulByConstantConstantModulusInPlace(modulus : BigInt, constant : BigInt, xs : LittleEndian) : Unit {
        body (...) {
            (Controlled ModularMulByConstantConstantModulusInPlace)(new Qubit[0], (modulus, constant, xs));
        }
        controlled (controls, ...) {
            EqualityFactL(GreatestCommonDivisorL(constant, modulus), 1L, 
                $"Cannot multiply by {constant} in-place modulo {modulus} because they are not co-prime"
            );
            let constantinv = InverseModL(constant, modulus);
            using (ys = Qubit[Length(xs!)]){
                let ysLE = LittleEndian(ys);
                (Controlled SwapLE)(controls, (xs, ysLE));
                (Controlled ModularMulByConstantConstantModulus)(controls, (modulus, constant, ysLE, xs));
                (Adjoint Controlled ModularMulByConstantConstantModulus)(controls, (modulus, constantinv, xs, ysLE));
            }
        }
        adjoint controlled auto;
    }
 


    ////////////////////////////////////////////////////////////////////////////////////////////
    ///////																				////////
    ///////                          MONTGOMERY ARITHMETIC                              ////////
    ///////																				////////
    ////////////////////////////////////////////////////////////////////////////////////////////

    /// These operations create, measure, and operate on modular integers encoded in Montgomery
    /// form, meaning an integer x is encoded as x2^n mod m, where n is the number of bits of m


    /// # Summary
    /// To represent Montgomery representations of modular integers
    /// xR mod m
    ///
    /// # Contents
    /// (LittleEndian, BigInt)=(x, m)
    newtype MontModInt = (modulus : BigInt, register : LittleEndian);

    /// # Summary
    /// Encodes a classical integer x into Montgomery form
    /// modulo m with respect to an integer 2^n, where n
    /// is the bitlength of x, and 2 is assumed coprime to m.
    /// Returns a MontModInt type containing the qubits
    /// containing the encoding, and m.
    ///
    /// # Inputs
    /// ## modulus
    /// Modulus m
    /// ## constant
    /// Input integer x
    /// ## register
    /// Qubit register for the encoding xR mod m
    operation CreateBigIntInMontgomeryForm(modulus : BigInt, constant : BigInt, register : LittleEndian) : MontModInt{
        Fact(modulus % 2L == 1L, $"Modulus must be odd for Montgomery form");
        let nQubits = BitSizeL(modulus);
        Fact(nQubits <= Length(register!), $"Cannot create Montgomery integer modulo {modulus} with only {Length(register!)} qubits");
        if (nQubits < Length(register!)){
            Message($"Warning : Too many qubits to initialize MontModInt; only the first {nQubits} of {Length(register!)} will be used");
        }
        let montgomeryR = 2L ^ nQubits % modulus;
        ApplyXorInPlaceL((montgomeryR * constant) % modulus, register);
        return MontModInt(modulus, LittleEndian(register![0..nQubits - 1]));
    }

    /// # Summary
    /// Encodes a classical integer x into Montgomery form
    /// modulo m with respect to an integer 2^n, where n
    /// is the bitlength of x, and 2 is assumed coprime to m.
    /// The result is XORed into a pre-existing MontModInt.
    ///
    /// # Inputs
    /// ## constant
    /// Input integer x
    /// ## montgomeryregister
    /// Qubit register for the encoding xR mod m.
    ///
    /// # Remarks
    /// The modulus is already included in `montgomeryRegister`, and that is
    /// the modulus used.
    operation EncodeBigIntInMontgomeryForm(constant : BigInt, montgomeryRegister : MontModInt) : Unit {
        body (...){
            let modulus = montgomeryRegister::modulus;
            Fact(Length(montgomeryRegister::register!)==BitSizeL(modulus), 
                $"Wrong number of qubits : {Length(montgomeryRegister::register!)} qubits for numbers modulo {modulus}"
            );
            let montgomeryR = 2L ^ Length(montgomeryRegister::register!) % modulus;
            EqualityFactL(GreatestCommonDivisorL(modulus, montgomeryR), 1L, $"Montgomery multiplier {montgomeryR} must be co-prime to the modulus {modulus}");
            ApplyXorInPlaceL((montgomeryR * constant) % modulus, montgomeryRegister::register);
        }
        adjoint controlled auto;
    }
    
    
    /// # Summary
    /// Encodes a quantum register `x` into Montgomery form
    /// modulo m with respect to 2^n, where n is the number
    /// of qubits in `x`, and 2 is assumed coprime to m.
    /// Returns a MontModInt type containing the qubits
    /// containing the encoding, and m.
    ///
    /// # Inputs
    /// ## modulus
    /// Modulus m.
    /// ## xs
    /// Qubit register with input x.
    ///
    /// #Output
    /// ## MontModInt
    /// A tuple containing xR mod m as a LittleEndian, 
    /// and modulus as a BigInt.
    operation EncodeQubitsInMontgomery(modulus : BigInt, xs : LittleEndian) : MontModInt {
        Fact(modulus % 2L == 1L, $"Modulus must be odd for Montgomery form");
        let montgomeryR = 2L ^ Length(xs!) % modulus;
        EqualityFactL(GreatestCommonDivisorL(modulus, montgomeryR), 1L, 
            $"Montgomery multiplier {montgomeryR} must be co-prime to the modulus {modulus}"
        );
        ModularMulByConstantConstantModulusInPlace(modulus, montgomeryR, xs);
        return MontModInt(modulus, xs);
    }

    /// # Summary
    /// Decodes a quantum register x from Montgomery form
    /// If the quantum register contains xR mod m, 
    /// this will set the quantum register to x mod m.
    ///
    /// # Inputs
    /// ## integer
    /// Quantum register to be decoded
    ///
    /// # Output
    /// ## LittleEndian 
    /// Points to the same register as `integer`, which is no longer 
    /// in Montgomery form.
    operation DecodeQubitsFromMontgomery(integer : MontModInt) : LittleEndian {
        let (modulus, xs) = integer!;
        let montgomeryRInv = InverseModL(2L ^ Length(xs!), modulus);
        ModularMulByConstantConstantModulusInPlace(modulus, montgomeryRInv, xs);
        return xs;
    }

    /// # Summary
    /// Given a quantum register x in Montgomery form, 
    /// as xR mod m, returns x mod m as a BigInt
    ///
    /// # Inputs
    /// ## integer
    /// Qubit register to be measured and decoded.
    ///
    /// #Output
    /// ##BigInt
    /// The result x mod m
    ///
    /// #Remarks
    /// Resets the register in `integer` to be all-zeros
    operation MeasureMontgomeryInteger(integer : MontModInt) : BigInt { 
        let (modulus, xs) = integer!;
        let xAsInt = MeasureBigInteger(xs);
        let montgomeryRInv = InverseModL(2L ^ Length(xs!), modulus);
        return (xAsInt * montgomeryRInv) % modulus;
    }


    function AssertModuliEqual(xs:MontModInt,ys:MontModInt):Unit {
        Fact(xs::modulus == ys::modulus,
            $"Binary operations on Montgomery encodings require 
             consistent moduli. Given {xs::modulus} and {ys::modulus}."
        );
    }


    /// # Summary
    /// Copies (with CNOTs) the qubit values from one MontModInt 
    /// type to another
    ///
    /// # Inputs
    /// ## input
    /// Qubit register whose value will be copied
    /// ## output
    /// Qubit register whose value will be XORed, bitwise, with 
    /// `input`.
    operation CopyMontModInt(input : MontModInt, output : MontModInt) : Unit {
        body (...){
            CopyLittleEndian(input::register, output::register);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place modular addition of two integers encoded in Montgomery 
    /// form modulo a constant integer `modulus`. Given two n-bit integers x and
    /// y encoded in MontModInt registers `xs` and `ys` the operation computes 
    /// the sum x + y mod modulus. The result is held in the register `ys`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y.
    operation ModularAddMontgomeryForm(xs : MontModInt, ys : MontModInt) : Unit {
        body(...){
            AssertModuliEqual(xs,ys);
            ModularAddConstantModulus(xs::modulus, xs::register, ys::register);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Given two inputs x and y, changes them to x-y and x+y, in place.
    ///
    /// # Inputs
    /// ## inputToMinus
    /// Qubit register containing x that will be returned containing x-y.
    /// ## inputToPlus
    /// Qubit register containing y that will be returns containing x+y.
    operation CrissCrossMontgomeryForm(inputToMinus : MontModInt, inputToPlus : MontModInt) : Unit {
        body (...){
            ModularAddMontgomeryForm(inputToMinus, inputToPlus);
            ModularDblMontgomeryForm(inputToMinus);
            (Adjoint ModularAddMontgomeryForm)(inputToPlus, inputToMinus);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place modular doubling of an integer modulo another 
    /// integer. Given an $n$-bit integer x encoded in Montgomery form 
    /// `xs`  the operation computes the double 2*x = x + x \mod m, 
    /// where `xs` stores the modulus m.
    /// The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer, is replaced with 
    /// 2x \mod m.
    ///
    /// # Remarks
    /// The algorithm only works
    /// correctly for odd moduli. For even modulus, the ancilla qubits
    /// will not necessarily be returned in the zero state.
    operation ModularDblMontgomeryForm (xs : MontModInt) : Unit {
        body (...){
            ModularDblConstantModulus(xs::modulus, xs::register);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place modular addition of an integer constant to an integer x
    /// encoded in Montgomery form in a qubit register `xs`, modulo `xs`'s integer constant `modulus`.
    ///
    /// # Description
    /// Given the n-bit integer x encoded in Montgomery the register `xs`, this operation computes
    /// x + constant * 2^n mod modulus, where n is the number of qubits in `xs`, and
    /// the result is held in the register `xs`.
    ///
    /// # Input
    /// ## constant
    /// Constant integer summand, not in Montgomery form.
    /// ## xs
    /// Qubit register encoding the first integer x.
    operation ModularAddConstantMontgomeryForm(constant : BigInt, xs : MontModInt) : Unit {
        body (...){
            let constantmont = (constant * (2L ^ Length(xs::register!))) % xs::modulus;
            ModularAddConstantConstantModulus(constantmont, xs::modulus, xs::register);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place modular negation of an integer modulo a constant
    /// integer modulus. 
    ///
    /// # Description
    /// Given an n-bit integer x encoded in Montgomery form 
    /// `xs` containing a constant integer `modulus`, the operation computes the negative  
    /// -x mod m. The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer x, is replaced with 
    /// the negative modulo `modulus`.
    operation ModularNegMontgomeryForm(xs : MontModInt) : Unit {
        body(...){
            ModularNegConstantModulus(xs::modulus, xs::register);
        }
        adjoint controlled auto;
    }

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
    /// # Remarks
    /// Since this operation relies on the operation ModularDblConstantModulus, 
    /// it only works correctly for odd moduli.
    operation ModularMulMontMontgomeryForm (xs : MontModInt, ys : MontModInt, blankOutputs : MontModInt) : Unit {
        body (...){
            ModularMulMontgomeryFormWindowedGeneric(CopyMontModInt(_, blankOutputs), xs, ys);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Multiplies two quantum registers modulo a classical modulus, 
    /// with a built-in Montgomery reduction by a factor of $2^{-n}$, 
    /// where n is the number of qubits for each input. It XORs the 
    /// the result into a third register.
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
    /// ## output
    /// The output register, which is XORed with
    /// `xs`*`ys`.
    operation ModularMulAndXorMontgomeryForm(xs : MontModInt, ys : MontModInt, outputs : MontModInt) : Unit{
        body (...){
            //Note that the double-and-add will not work with XOR, so that's why this is separate from
            // ModularMulConstantModulus.
            ModularMulMontgomeryFormWindowedGeneric(CopyMontModInt(_, outputs), xs, ys);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Multiplies two quantum registers modulo a classical modulus, 
    /// with a built-in Montgomery reduction by a factor of $2^-{n}$, 
    /// where n is the number of qubits for each input.
    /// The result is added to the output register.
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
    /// ## output
    /// The output register, to which `xs`*`ys` is
    /// added.
    operation ModularMulAndAddMontgomeryForm(xs : MontModInt, ys : MontModInt, outputs : MontModInt) : Unit{
        body (...){
            ModularMulMontgomeryFormWindowedGeneric(ModularAddMontgomeryForm(_, outputs), xs, ys);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Given a qubit registers `xs` containing a modular integer in 
    /// Montgomery form, computes the inverse of `xs`
    /// and copies the result to `outputs` (assumed to be blank).
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register containing the number to be inverted
    /// ## blankOutputs
    /// Qubit register where the result will be output (must be 0s).
    operation ModularInvertAndCopyMontgomeryForm(xs : MontModInt, blankOutputs : MontModInt) : Unit {
        body (...){
            let DoubleWithMontModInt = DummyIntegerWrapper(Adjoint ModularDblMontgomeryForm, blankOutputs, _);
            InvertBitShiftConstantModulusGeneric(CopyMontModInt(_, blankOutputs), DoubleWithMontModInt, xs);
        }
        controlled adjoint auto;
    }
    
    /// # Summary
    /// Given two qubit registers `xs` and `outputs` containing modular integers in 
    /// Montgomery form, computes the inverse of `xs` and adds the result to `outputs`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register containing the number to be inverted
    /// ## outputs
    /// Qubit register containing the number the inverse will be added to.
    ///
    /// # Remarks
    /// This is a wrapper for InvertBitShiftsConstantModulus.
    operation ModularInvertAndAddMontgomeryForm(xs : MontModInt, outputs : MontModInt) : Unit {
        body (...){
            let DoubleWithMontModInt = DummyIntegerWrapper(Adjoint ModularDblMontgomeryForm, outputs, _);
            InvertBitShiftConstantModulusGeneric(ModularAddMontgomeryForm(_, outputs), DoubleWithMontModInt, xs);
        }
        controlled adjoint auto;
    }

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
    operation ModularDivideAndAddMontgomeryForm(xs : MontModInt, ys : MontModInt, outputs : MontModInt) : Unit{
        body (...) {
            let DoubleWithMontModInt = DummyIntegerWrapper(Adjoint ModularDblMontgomeryForm, outputs, _);
            InvertBitShiftConstantModulusGeneric(ModularMulAndAddMontgomeryForm(_, ys, outputs), DoubleWithMontModInt, xs);
        }
        controlled adjoint auto;
    }


    //////////////       Internal Functions     ///////////////////

    /// # Summary
    /// Multiplies two integers encoded in qubit registers in Montgomery
    /// form. Requires n + 1 clean ancilla which are returned dirty.
    ///
    /// #Inputs
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
    /// # References
    /// - The circuit is Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///   This implementation uses 2 carry qubits
    /// 
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation ModularMulMontgomeryFormOpen (xs : MontModInt, ys : MontModInt, ancillas : Qubit[], blankOutputs : MontModInt) : Unit{
        body (...){
            let modulus = xs::modulus;
            let xsLE = xs::register;
            let ysLE = ys::register;
            let outputsLE = blankOutputs::register;
            let nQubits = Length(xs::register!);
            let (nSelfAncilla, nSelfOutputs) = AncillaCountModularMulMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Montgomery multiplication ancila:", ancillas);
            AssertEnoughQubits(nSelfOutputs, "Montgomery multiplication output: ", blankOutputs::register!);
            let ms = ancillas[0 .. nQubits - 1];
            
            using ((ysCarry, testCarry) = (Qubit[1], Qubit())){//only necessary to match the number of qubits for the adder
                let carries = [ancillas[nQubits], testCarry];
                for (idxBit in 0..nQubits-1){
                    (Controlled AddInteger)([xsLE![idxBit]], (LittleEndian(ysLE! + ysCarry), LittleEndian(outputsLE! + [carries[0]]), carries[1]));
                    CNOT(outputsLE![0], ms[idxBit]);
                    (Controlled AddConstant)([ms[idxBit]], (modulus, LittleEndian(outputsLE! + carries)));
                    (Adjoint CyclicRotateRegister)(LittleEndian(outputsLE! + carries));

                }
                (Adjoint AddConstant)(modulus, LittleEndian(outputsLE! + [carries[0]]));
                (Controlled AddConstant)([carries[0]], (modulus, outputsLE));
            }
        }
        controlled auto;
        adjoint auto;
        controlled adjoint auto;
    }

    
    /// # Summary
    /// Given an input index t, an odd modulus p, and a bit length k,
    /// computes an integer m such that pm = -t mod 2^k, and then 
    /// writes pm (not modulo 2^k) into the output register
    ///
    /// # Inputs
    /// ## index
    /// The index t
    /// ## bitLength
    /// The bitlength k 
    /// ## modulus
    /// The odd modulus p
    /// ## register
    /// The quantum outut register. Should have |p| + k bits
    ///
    /// # Remarks
    /// Used for windowed Montgomery multiplication: We do a quantum
    /// look-up based on the low k bits of some intermediate value;
    /// this simulates a "table" of the values pm. If these values are
    /// added to the look-up register, it clears the lower k bits.
    operation WriteLowBitClearingMultiple(index : BigInt, bitLength : Int, modulus : BigInt, register : LittleEndian) : Unit {
        body (...){
            (Controlled WriteLowBitClearingMultiple)(new Qubit[0], (index, bitLength, modulus, register));
        }
        controlled (controls, ...){
            let newIndex = 2L^bitLength - index;
            let inverseModulus = (newIndex * InverseModL(modulus, 2L^bitLength)) % 2L^bitLength;
            let clearingInteger = modulus * inverseModulus;
            (Controlled ApplyXorInPlaceL)(controls, (clearingInteger, register));
        }
        adjoint controlled auto;
    }   

    /// # Summary
    /// Multiplies two integers encoded in qubit registers in Montgomery
    /// form. Requires n + 1 clean ancilla which are returned dirty.
    /// Uses a windowing technique for lower depth, using an extra
    /// n + k qubits for n-bit inputs and a k-bit window.
    ///
    /// #Inputs
    /// ## windowSize
    /// The bit size of the windows used
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
    /// # References
    /// - The circuit is Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///   This implementation uses 2 carry qubits
    /// 
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception. 
    operation ModularMulMontgomeryFormWindowedOpen (windowSize : Int, xs : MontModInt, ys : MontModInt, ancillas : Qubit[], blankOutputs : MontModInt) : Unit{
        body (...){
            if (windowSize == 0){//to give expected behaviour for window size of 0
                ModularMulMontgomeryFormOpen(xs, ys, ancillas, blankOutputs);
            } else {
                let modulus = xs::modulus;
                let xsLE = xs::register;
                let ysLE = ys::register;
                let outputsLE = blankOutputs::register;
                let nQubits = Length(xs::register!);
                let (nSelfAncilla, nSelfOutputs) = AncillaCountModularMulMontgomeryForm(nQubits);
                AssertEnoughQubits(nSelfAncilla, "Montgomery multiplication ancilla:", ancillas);
                AssertEnoughQubits(nSelfOutputs, "Montgomery multiplication output: ", blankOutputs::register!);
                let ms = ancillas[0 .. nQubits - 1];
                let carry = ancillas[nQubits];
                using (ysCarry = Qubit[1]){//only necessary to match the number of qubits for the adder
                    let nWindows = nQubits / windowSize + 1 - BoolArrayAsInt([nQubits % windowSize == 0]);
                    for (idxWindow in 0 .. nWindows - 1){
                        let currentWindowSize = MinI(windowSize, nQubits - idxWindow * windowSize);// max possible window size
                        // Allocates extra qubits for carries, which are cleared with every window
                        using (outputAncillas = Qubit[currentWindowSize]){
                            // Bookkeeping of ancilla
                            let outputs = outputsLE! + [carry] + outputAncillas;
                            let smallOutputs = outputsLE! + [carry] + outputAncillas[0.. currentWindowSize - 2];
                            let lastOutput = outputAncillas[currentWindowSize - 1];
                            // This loop does a naive multiplication of windowSize bits of x
                            // and the entire integer y, adding the result to the output register
                            for (idxWindowBit in 0 .. currentWindowSize - 1){
                                // get n+1 bits 
                                let roundOutputs = LittleEndian(outputs[idxWindowBit .. idxWindowBit + nQubits]);
                                (Controlled AddInteger)(
                                    [xsLE![idxWindowBit + idxWindow * windowSize]], 
                                    (
                                        LittleEndian(ysLE! + ysCarry), 
                                        roundOutputs, 
                                        outputs[idxWindowBit + nQubits + 1]
                                    )
                                );
                            }
                            // Copies the low order bits to the ancilla ms
                            let address = LittleEndian(ms[idxWindow * windowSize .. idxWindow * windowSize + currentWindowSize - 1]);
                            
                            CopyLittleEndian(
                                LittleEndian(outputs[0 .. currentWindowSize - 1]),
                                address
                            );
                            // Uses the bits in m to look up which value to write unto a modulus register
                            // Adds that register to the outputs to clear the low bits
                            // Possible future improvement: an "EqualLookup" that takes a function, rather than
                            // an array
                            using (modulusQubits = Qubit[nQubits + currentWindowSize]){
                                let modulusMultiple = LittleEndian(modulusQubits);
                                let bigIntSequence = Microsoft.Quantum.Arrays.SequenceL(0L, 2L^currentWindowSize - 1L);
                                EqualLookup(bigIntSequence, WriteLowBitClearingMultiple(_, currentWindowSize, modulus, modulusMultiple), address);
                                AddInteger(modulusMultiple, LittleEndian(smallOutputs), lastOutput);
                                (Adjoint EqualLookup)(bigIntSequence, WriteLowBitClearingMultiple(_, currentWindowSize, modulus, modulusMultiple), address); 
                            }
                            // Shifts the register back, so the high bits are clear
                            (Adjoint CyclicRotateRegisterMultiple)(LittleEndian(outputs), currentWindowSize);
                        }
                    }
                    // Final adjustment
                    (Adjoint AddConstant)(modulus, LittleEndian(outputsLE! + [carry]));
                    (Controlled AddConstant)([carry], (modulus, outputsLE));
                }
            }
        }
        controlled auto;
        adjoint auto;
        controlled adjoint auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open modular multiplication
    /// in Montgomery form.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the integers being multiplied
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountModularMulMontgomeryForm (nQubits : Int) : (Int, Int) {
        return (nQubits + 1, nQubits);
    }

    /// # Summary
    /// Multiplies two quantum registers modulo a classical modulus, 
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
    /// ## xs
    /// The first quantum input to the product.
    /// Returned unchanged.
    /// ## ys 
    /// The second quantum input to the product.
    /// Returned unchanged.
    ///
    /// # References
    /// - The circuit is Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    operation ModularMulMontgomeryFormGeneric(copyop : ((MontModInt) => Unit is Ctl + Adj), xs : MontModInt, ys : MontModInt) : Unit {
        body (...) {
            (Controlled ModularMulMontgomeryFormGeneric)(new Qubit[0], (copyop, xs, ys));
        }
        controlled (controls, ...){
            let modulus = xs::modulus;
            let nQubits=Length(xs::register!);
            let (nAncilla, nOutputs) = AncillaCountModularMulMontgomeryForm(nQubits);
            using((ancillas, outputs) = (Qubit[nAncilla], Qubit[nOutputs])){
                let innerzs = MontModInt(modulus, LittleEndian(outputs));       
                ModularMulMontgomeryFormOpen(xs, ys, ancillas, innerzs);
                /// Since we reverse the main body of the circuit, this is the only
                ///section that actually needs to be controlled, 
                ///which saves on Toffolis
                (Controlled copyop)(controls, (innerzs));
                (Adjoint ModularMulMontgomeryFormOpen)(xs, ys, ancillas, innerzs);
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Chooses an optimal window size for windowed multiplication
    /// of a given size. References the global cost metric to decide.
    /// 
    /// # Inputs
    /// ## nQubits
    /// The bit-size of the inputs to the multiplication
    function OptimalMultiplicationWindowSize(nQubits : Int) : Int {
        if (nQubits <= 3){//simple base case
            return 0;
        }
        let lgn = Microsoft.Quantum.Math.Log(IntAsDouble(nQubits)) / Microsoft.Quantum.Math.Log(2.0);
        if (IsMinimizeDepthCostMetric()) {
            if (nQubits < 4){
                return 0;
            } else {
                let log2 = Microsoft.Quantum.Math.Log(2.0);
                let lglgn = Microsoft.Quantum.Math.Log(Microsoft.Quantum.Math.Log(IntAsDouble(nQubits)) / log2) / log2;
                //Extrapolated from known values
                return Max([0, Microsoft.Quantum.Math.Ceiling(1.97*lglgn - 1.11 - 0.5)]);//extra 0.5 is to turn ceiling to round
            }
        } elif (IsMinimizeTCostMetric()) {
            //Extrapolated from known values
            return Microsoft.Quantum.Math.Ceiling(lgn * 0.68  + 0.12 - 0.5);//extra 0.5 is to turn ceiling to round
        } elif (IsMinimizeWidthCostMetric()) {
            // This returns 0 so there is no windowing
            // This is the width-minimal option
            // The other formula is for minimizing T count, subject to the width-minimizing adders, etc.
            // Within elliptic curve addition, we have the qubits to spare, so it makes sense to use the extra width
            // for this
            //return 0;

            //This minimizes T count 
            return Microsoft.Quantum.Math.Ceiling(lgn * 0.75  + 0.78 - 0.5);//extra 0.5 is to turn ceiling to round
        } else {
            return 0;   
        }
    }

    /// # Summary
    /// Multiplies two quantum registers modulo a classical modulus, 
    /// with a built-in Montgomery reduction by a factor of $2^{-n}$, 
    /// where $n$ is the number of qubits for each input.
    ///
    /// It processes the output with an operation passed by 
    /// the user, before uncomputing the multiplication.
    ///
    /// Uses windowed multiplication and calls a function
    /// to pick the window size.
    ///
    /// #Inputs
    /// ## copyop
    /// The operation will give `copyop` the register $\ket{x*y mod m}$
    /// as input, and assumes that `copyop` leaves the input
    /// register unchanged.
    /// ## xs
    /// The first quantum input to the product.
    /// Returned unchanged.
    /// ## ys 
    /// The second quantum input to the product.
    /// Returned unchanged.
    ///
    /// # References
    /// - The circuit is Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    operation ModularMulMontgomeryFormWindowedGeneric(copyop : ((MontModInt) => Unit is Ctl + Adj), xs : MontModInt, ys : MontModInt) : Unit {
        body (...) {
            (Controlled ModularMulMontgomeryFormWindowedGeneric)(new Qubit[0], (copyop, xs, ys));
        }
        controlled (controls, ...){
            let modulus = xs::modulus;
            let nQubits=Length(xs::register!);
            let (nAncilla, nOutputs) = AncillaCountModularMulMontgomeryForm(nQubits);
            using((ancillas, outputs) = (Qubit[nAncilla], Qubit[nOutputs])){
                let innerzs = MontModInt(modulus, LittleEndian(outputs));
                let windowSize = OptimalMultiplicationWindowSize(nQubits);
                ModularMulMontgomeryFormWindowedOpen(windowSize, xs, ys, ancillas, innerzs);                    
                /// Since we reverse the main body of the circuit, this is the only
                ///section that actually needs to be controlled, 
                ///which saves on Toffolis
                (Controlled copyop)(controls, (innerzs));
                (Adjoint ModularMulMontgomeryFormWindowedOpen)(windowSize, xs, ys, ancillas, innerzs);
            }
        }
        adjoint controlled auto;
    }


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
    /// # References
    /// - The circuit is a classical-optimized version of Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remarks
    /// Currently optimized based on carry lookahead adder costs.
    ///
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation MulByConstantMontgomeryFormOpen(constant : BigInt, xs : MontModInt,  ancillas : Qubit[], blankOutputs : MontModInt) : Unit {
        body (...){
            let nQubits = Length(xs::register!);
            let modulus = xs::modulus;
            let constantMontgomery = (constant * 2L ^ nQubits) % modulus;
            let constantArray = BigIntAsBoolArray(constantMontgomery);
            let numOneBits = HammingWeightL(constantMontgomery);
            let (nSelfAncilla, nSelfOutputs) = AncillaCountConstantMulMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Montgomery constant multiplication ancilla: ", ancillas);
            AssertEnoughQubits(nSelfOutputs, "Montgomery constant multiplication outputs: ", blankOutputs::register!);
            // A single controlled addition by a constant uses 9n+o(n) Toffoli gates
            // An uncontrolled addition of two quantum registers uses 10n+o(n) Toffoli gates
            // (depths are nearly identical)
            // Thus, if the number of 1 bits in the constant is less than 9/10 * number of bits
            // Then it is more cost effective to add uncontrolled
            if (9 * nQubits < 10 * numOneBits){
                (Controlled MulByConstantMontgomeryFormOpen)(new Qubit[0], (constant, xs, ancillas, blankOutputs));
            } else {
                // Ancilla bookkeeping
                let carries = ancillas[nQubits .. nQubits + 1];
                let outputOneCarry = LittleEndian(blankOutputs::register! + [carries[0]]);
                let outputTwoCarries = LittleEndian(blankOutputs::register!+carries);
                // The input requires an extra qubit to match the output
                using (xCarry = Qubit[1]){
                    let xsOneCarry = LittleEndian(xs::register! + xCarry);
                    for (idx in 0..nQubits - 1){
                        //Small constants will produce small arrays
                        //This simulates leading zeros
                        if (Length(constantArray) > idx){
                            if (constantArray[idx]){
                                AddInteger(xsOneCarry, outputOneCarry, carries[1]);
                            }
                        }
                        CNOT((blankOutputs::register!)[0], ancillas[idx]);
                        (Controlled AddConstant)([ancillas[idx]], (modulus, outputTwoCarries));
                        (Adjoint CyclicRotateRegister)(outputTwoCarries);
                    }
                    (Adjoint AddConstant)(modulus, outputTwoCarries);
                    (Controlled AddConstant)([carries[0]], (modulus, blankOutputs::register));
                }
            }
        }
        controlled (controls,...){
            let nQubits = Length(xs::register!);
            let modulus = xs::modulus;
            let constantMontgomery = (constant * 2L ^ nQubits) % modulus;
            let constantArray = BigIntAsBoolArray(constantMontgomery);
            let numOneBits = HammingWeightL(constantMontgomery);
            let (nSelfAncilla, nSelfOutputs) = AncillaCountConstantMulMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Montgomery constant multiplication ancilla: ", ancillas);
            AssertEnoughQubits(nSelfOutputs, "Montgomery constant multiplication outputs: ", blankOutputs::register!);
            // Ancilla bookkeeping
            let carries = ancillas[nQubits .. nQubits + 1];
            let outputOneCarry = LittleEndian(blankOutputs::register! + [carries[0]]);
            let outputTwoCarries = LittleEndian(blankOutputs::register!+carries);
            // The input requires an extra qubit to match the output
            // This is only used in the second if, but it would be 
            // difficult to conditionally allocate a qubit.
            using (xCarry = Qubit[1]){
                let xsOneCarry = LittleEndian(xs::register! + xCarry);
                for (idx in 0..nQubits - 1){
                    // A single controlled addition by a constant uses 9n+o(n) Toffoli gates
                    // A single controlled addition of two quantum registers uses 12n+o(n) Toffoli gates
                    // This chooses the cheaper option based on the Hamming weight
                    if (9 * nQubits < 12 * numOneBits){
                        (Controlled AddConstant)(controls + [(xs::register!)[idx]], (constantMontgomery, outputTwoCarries));
                    } else {
                        //Small constants will produce small arrays
                        //This simulates leading zeros
                        if (Length(constantArray) > idx){
                            if (constantArray[idx]){
                                (Controlled AddInteger)(controls, (xsOneCarry, outputOneCarry, carries[1]));
                            }
                        }
                    }
                    CNOT((blankOutputs::register!)[0], ancillas[idx]);
                    (Controlled AddConstant)([ancillas[idx]], (modulus, outputTwoCarries));
                    (Adjoint CyclicRotateRegister)(outputTwoCarries);	
                }
            }
            (Controlled Adjoint AddConstant)(controls, (modulus, outputTwoCarries));
            (Controlled AddConstant)([carries[0]], (modulus, blankOutputs::register));
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open modular 
    /// mulitplication by a constant for a qubit in Montgomery form.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the quantum integer being multiplied
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountConstantMulMontgomeryForm (nQubits : Int) : (Int, Int) {
        return (nQubits + 2, nQubits);
    }


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
    /// # References
    /// - The circuit is Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    operation MulByConstantMontgomeryFormGeneric(copyop : (MontModInt=>Unit is Ctl + Adj), constant:BigInt, xs:MontModInt):Unit {
        body (...){
            (Controlled MulByConstantMontgomeryFormGeneric)(new Qubit[0], (copyop, constant, xs));
        }
        controlled (controls,...){
            let nQubits = Length(xs::register!);
            let (nMulAncilla, nMulOutputs) = AncillaCountConstantMulMontgomeryForm(nQubits);
            using ((ancillas, outputs) = (Qubit[nMulAncilla], Qubit[nMulOutputs])){
                let productMontModInt = MontModInt(xs::modulus, LittleEndian(outputs));
                MulByConstantMontgomeryFormOpen(constant, xs, ancillas, productMontModInt);
                (Controlled copyop)(controls, (productMontModInt));
                (Adjoint MulByConstantMontgomeryFormOpen)(constant, xs, ancillas, productMontModInt);
            }
        }
        controlled adjoint auto;
    }

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
    /// # References
    /// - The circuit is roughly Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation ModularSquMontgomeryFormOpen (xs : MontModInt, ancillas : Qubit[], blankOutputs : MontModInt) : Unit{
        body (...){
            let modulus = xs::modulus;
            let nQubits = Length(xs::register!);
            let xsLE = xs::register;
            let outputsLE = blankOutputs::register;

            let (nSelfAncilla, nSelfOutput) = AncillaCountModularSquMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfOutput, "Montgomery square output: ", blankOutputs::register!);
            AssertEnoughQubits(nSelfAncilla, "Montgomery square ancilla: ", ancillas);
            let ms = ancillas[0 .. nQubits - 1];
            using ((xControl, xsCarry, testCarry) = (Qubit(), Qubit[1], Qubit())){//only necessary to match the number of qubits for the TTK adder
                let carries = [ancillas[nQubits], testCarry];
                for (idxBit in 0..nQubits-1){
                    CNOT((xs::register)![idxBit], xControl);
                    (Controlled AddInteger)([xControl], (LittleEndian(xsLE! + xsCarry), LittleEndian(outputsLE! + [carries[0]]), carries[1]));
                    CNOT((xs::register)![idxBit], xControl);
                    CNOT(outputsLE![0], ms[idxBit]);
                    (Controlled AddConstant)([ms[idxBit]], (modulus, LittleEndian(outputsLE! + carries)))   ;
                    (Adjoint CyclicRotateRegister)(LittleEndian(outputsLE! + carries));
                }
                (Adjoint AddConstant)(modulus, LittleEndian(outputsLE! + [carries[0]]));
                (Controlled AddConstant)([carries[0]], (modulus, outputsLE));
            }
        }
        controlled auto;
        adjoint auto;
        controlled adjoint auto;
    }

    /// # Summary
    /// Chooses an optimal window size for windowed squaring
    /// of a given size. References the global cost metric to decide.
    /// 
    /// # Inputs
    /// ## nQubits
    /// The bit-size of the inputs to the squaring
    function OptimalSquaringWindowSize(nQubits : Int) : Int {
        //Currently not optimized directly;
        // we assume it has the same optimum as multiplication
        return OptimalMultiplicationWindowSize(nQubits);
    }
    
    /// # Summary
    /// Squares an integer modulo a classical
    /// modulus, using Montgomery mulitplication.
    /// Requires n + 2 clean ancilla, which are returned 
    /// dirty.
    /// Uses a windowing technique for lower depth, using an extra
    /// n + k qubits for n-bit inputs and a k-bit window.
    ///
    /// #Inputs
    /// ## windowSize
    /// The bit size of the windows used
    /// ## xs
    /// The register to be squared.
    /// ## ancillas
    /// Clean ancillas that will be returned dirty. 
    /// ## blankOutputs
    /// A register input with all zeros, which will contain
    /// the intermediate result before uncomputing.
    ///
    /// # References
    /// - The circuit is roughly Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation ModularSquMontgomeryFormWindowedOpen (windowSize : Int, 
        xs : MontModInt, 
        ancillas : Qubit[], 
        blankOutputs : MontModInt
    ) : Unit{
        body (...){
            if (windowSize == 0){//to give expected behaviour for window size of 0
                ModularSquMontgomeryFormOpen(xs, ancillas, blankOutputs);
            } else {
                let modulus = xs::modulus;
                let xsLE = xs::register;
                let outputsLE = blankOutputs::register;
                let nQubits = Length(xs::register!);
                let (nSelfAncilla, nSelfOutput) = AncillaCountModularSquMontgomeryForm(nQubits);
                AssertEnoughQubits(nSelfOutput, "Montgomery square output: ", blankOutputs::register!);
                AssertEnoughQubits(nSelfAncilla, "Montgomery square ancilla: ", ancillas);
                let ms = ancillas[0 .. nQubits - 1];
                let carry = ancillas[nQubits];
                using (xsCarry = Qubit[1]){//only necessary to match the number of qubits for the adder
                    let nWindows = nQubits / windowSize + 1 - BoolArrayAsInt([nQubits % windowSize == 0]);
                    for (idxWindow in 0 .. nWindows - 1){
                        let currentWindowSize = MinI(windowSize, nQubits - idxWindow * windowSize);// max possible window size
                        // Allocates extra qubits for carries, which are cleared with every window
                        using (outputAncillas = Qubit[currentWindowSize]){
                            // Bookkeeping of ancilla
                            let outputs = outputsLE! + [carry] + outputAncillas;
                            let smallOutputs = outputsLE! + [carry] + outputAncillas[0.. currentWindowSize - 2];
                            let lastOutput = outputAncillas[currentWindowSize - 1];
                            // This loop does a naive multiplication of windowSize bits of x
                            // and the entire integer y, adding the result to the output register
                            using (xControl = Qubit()){
                                for (idxWindowBit in 0 .. currentWindowSize - 1){
                                    // get n+1 bits 
                                    CNOT(xsLE![idxWindowBit + idxWindow * windowSize], xControl);
                                    let roundOutputs = LittleEndian(outputs[idxWindowBit .. idxWindowBit + nQubits]);
                                    (Controlled AddInteger)(
                                        [xControl], 
                                        (
                                            LittleEndian(xsLE! + xsCarry), 
                                            roundOutputs, 
                                            outputs[idxWindowBit + nQubits + 1]
                                        )
                                    );
                                    CNOT(xsLE![idxWindowBit + idxWindow * windowSize], xControl);
                                   // DumpQubits([xControl], "X control:");
                                }
                            }
                            // Copies the low order bits to the ancilla ms
                            let address = LittleEndian(ms[idxWindow * windowSize .. idxWindow * windowSize + currentWindowSize - 1]);
                            
                            CopyLittleEndian(
                                LittleEndian(outputs[0 .. currentWindowSize - 1]),
                                address
                            );
                            // Uses the bits in m to look up which value to write unto a modulus register
                            // Adds that register to the outputs to clear the low bits
                            // Possible future improvement: an "EqualLookup" that takes a function, rather than
                            // an array
                            using (modulusQubits = Qubit[nQubits + currentWindowSize]){
                                let modulusMultiple = LittleEndian(modulusQubits);
                                let bigIntSequence = Microsoft.Quantum.Arrays.SequenceL(0L, 2L^currentWindowSize - 1L);
                                EqualLookup(bigIntSequence, WriteLowBitClearingMultiple(_, currentWindowSize, modulus, modulusMultiple), address);
                                AddInteger(modulusMultiple, LittleEndian(smallOutputs), lastOutput);
                                (Adjoint EqualLookup)(bigIntSequence, WriteLowBitClearingMultiple(_, currentWindowSize, modulus, modulusMultiple), address); 
                               // DumpQubits(modulusQubits, "modulus qubits:");
                            }
                            // Shifts the register back, so the high bits are clear
                            (Adjoint CyclicRotateRegisterMultiple)(LittleEndian(outputs), currentWindowSize);
                            //DumpQubits(outputAncillas, "Output ancillas:");
                        }
                    }
                    // Final adjustment
                    (Adjoint AddConstant)(modulus, LittleEndian(outputsLE! + [carry]));
                    (Controlled AddConstant)([carry], (modulus, outputsLE));
                   // DumpQubits(       xsCarry, "Xs Carry:");
                }
            }
        }
        controlled auto;
        adjoint auto;
        controlled adjoint auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open modular squaring
    /// in Montgomery form.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the integer being squared
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountModularSquMontgomeryForm (nQubits : Int) : (Int, Int) {
        return (nQubits + 1, nQubits);
    }

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
    /// # References
    /// - The circuit is roughly Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    operation ModularSquMontgomeryFormGeneric (copyop : ((MontModInt) => Unit is Ctl + Adj), xs : MontModInt) : Unit {
        body (...) {
            (Controlled ModularSquMontgomeryFormGeneric)(new Qubit[0], (copyop, xs));
        }
        controlled (controls, ...){
            let modulus = xs::modulus;
            let nQubits=Length(xs::register!);
            let (nAncillas, nOutputs) = AncillaCountModularSquMontgomeryForm(nQubits);
            using((ancillas, outputQubits) = (Qubit[nAncillas], Qubit[nOutputs])){
                let innerzs = MontModInt(modulus, LittleEndian(outputQubits));
                ModularSquMontgomeryFormOpen(xs, ancillas, innerzs);
                /// Since we reverse the main body of the circuit, this is the only
                ///section that actually needs to be controlled
                (Controlled copyop)(controls, (innerzs));
                (Adjoint ModularSquMontgomeryFormOpen)(xs, ancillas, innerzs);
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Squares an integer modulo a classical
    /// modulus, using Montgomery mulitplication.
    /// The result is processed according to a 
    /// user-specified operation, then uncomputed.
    ///
    /// Uses windowed multiplication and calls a function
    /// to pick the window size.
    ///
    /// # Inputs
    /// ## copyop
    /// The operation applied to x^2 once it is
    /// computed, before it is uncomputed. It must
    /// not change the value in `xs`.
    /// ## xs
    /// Qubit register to be squared.
    ///
    /// # References
    /// - The circuit is roughly Fig. 7 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    operation ModularSquMontgomeryFormWindowedGeneric (copyop : ((MontModInt) => Unit is Ctl + Adj), xs : MontModInt) : Unit {
        body (...) {
            (Controlled ModularSquMontgomeryFormWindowedGeneric)(new Qubit[0], (copyop, xs));
        }
        controlled (controls, ...){
            //DumpLittleEndian(xs::register, "Input:");
            let modulus = xs::modulus;
            let nQubits=Length(xs::register!);
            let windowSize = OptimalSquaringWindowSize(nQubits);
            if (windowSize == 0){//treat 0 window size as no windowing
                (Controlled ModularSquMontgomeryFormGeneric)(controls, (copyop, xs));
            } else {
                let (nAncilla, nOutputs) = AncillaCountModularSquMontgomeryForm(nQubits);
                using((ancillas, outputs) = (Qubit[nAncilla], Qubit[nOutputs])){
                    let innerzs = MontModInt(modulus, LittleEndian(outputs));
                    ModularSquMontgomeryFormWindowedOpen(windowSize, xs, ancillas, innerzs);
                    /// Since we reverse the main body of the circuit, this is the only
                    ///section that actually needs to be controlled
                    (Controlled copyop)(controls, (innerzs));
                    (Adjoint ModularSquMontgomeryFormWindowedOpen)(windowSize, xs, ancillas, innerzs);
                //  DumpQubits(ancillas, "Ancillas: ");
                //  DumpQubits(outputs, "Outputs: ");
                }
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Executes a single round of a bit-wise inversion.
    /// 
    /// # Description
    /// If us contains an even integer, set `us` = `us`/2 and `ss` = 2*`ss`
    /// Else if vs contains an even integer, set `vs` = `vs`/2 and `rs` = 2*`rs`
    /// Else if `us`>`vs`, set `us` = (`us` - `vs`)/2, `ss`=2*`ss`, and `rs`=`rs`+`ss`
    /// Else set `vs` = (`vs` - `us`)/2, `rs`=2*`rs`, and `ss`=`rs`+`ss`
    ///
    /// #Inputs
    /// #us
    /// Register originally containing the modulus
    /// #vs
    /// Register originally containing the integer to invert
    /// #rs
    /// Register that will contain the pseudo-inverse
    /// #ss
    /// Ancilla register necessary for the GCD computation.
    /// #mi
    /// The ith qubit in a register of ancillas that track
    /// which function occured in this round.
    ///
    /// #References
    /// This is the boxed circuit from Figure 9 in : 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    /// The desired action is the main "while" loop from : 
    ///   Burton S. Kaliski, Jr. "The Montgomery Inverse and Its Applications"
    ///   https : //doi.org/10.1109/12.403725
    operation _MontBitGCDRound(indexm : Int, us : LittleEndian, vs : LittleEndian, rs : LittleEndian, ss : LittleEndian, ms : Qubit[]) : Unit {
        body(...){
            (Controlled _MontBitGCDRound)(new Qubit[0], (indexm, us, vs, rs, ss, ms));
        }
        controlled(controls, ...){
            if (Length(controls) > 1 ){
                Message($"Warning: GCD round called with {Length(controls)} controls");
            }
            using ((carry, aQubit, bQubit)=(Qubit(), Qubit(), Qubit())){
                //carry is the qubit in figure 9 between v and s
                //aqubit is the bottom qubit in figure 9, between r and m_i
                //bqubit is the top qubit in figure 9, between r and m_i
                //First negated CNOT : is u even?
                X(us![0]);
                CheckIfAllOnes(controls + [us![0]], aQubit);
                //(Controlled CNOT)(controls, (us![0], aQubit));
                X(us![0]);
                //Second negated CNOT : Is v even but u odd?
                X(vs![0]);
                X(aQubit);
                CheckIfAllOnes(controls + [vs![0],aQubit], ms[indexm]);
                //(Controlled CCNOT)(controls, (vs![0], aQubit, ms[indexm]));
                X(aQubit);
                X(vs![0]);
                //First comparison gate
                //TODO : Create a GreaterThan operation that 
                // takes an operation as an argument, so we 
                // can copy out the bit before uncomputing.
                // Currently it computes the carry, uncomputes, 
                // uses the carry, then computes the carry again
                // and uncomputes the comparison.
                GreaterThanWrapper(us, vs, carry);
                //Tree of CNOTS

                CNOT(aQubit, bQubit);
                CNOT(ms[indexm], bQubit);
                X(bQubit);
                CheckIfAllOnes(controls + [carry, bQubit], aQubit);
                CheckIfAllOnes(controls + [carry, bQubit], ms[indexm]);
                // (Controlled X)(controls+[carry, bQubit], (aQubit));
                // (Controlled X)(controls+[carry, bQubit], (ms[indexm]));
                X(bQubit);
                CNOT(ms[indexm], bQubit);
                CNOT(aQubit, bQubit);
                //Undo Comparison
                (Adjoint GreaterThanWrapper)(us, vs, carry);
                
                //To save on additions vs. Roetteler et al., 
                //we swap u and v, and r and s, based on a, 
                //since whether we halve u or v depends only 
                //on a
                (Controlled SwapLE)([aQubit], (us, vs));
                (Controlled SwapLE)([aQubit], (rs, ss));
                //We add iff the XOR of m_i and a is 0
                CNOT(ms[indexm], aQubit);
                X(aQubit);
                (Controlled Adjoint AddIntegerNoCarry)(controls+[aQubit], (us, vs));
                (Controlled AddIntegerNoCarry)(controls+[aQubit], (rs, ss));
                X(aQubit);
                CNOT(ms[indexm], aQubit);
                //Controlled cyclic shifts
                (Controlled Adjoint CyclicRotateRegister)(controls, (vs));
                (Controlled CyclicRotateRegister)(controls, (rs));
                //Controlled swap : Message("point 1");
                (Controlled SwapLE)([aQubit], (us, vs));
                (Controlled SwapLE)([aQubit], (rs, ss));
                //Uncompute "a" with the parity of r
                (Controlled X)(controls + [rs![0]], (aQubit));
            }
        }
        adjoint controlled auto;
    }




    /// # Summary
    /// Computes the pseudo-inverse of the contents in `us`, 
    /// modulo the integer `modulus`, using a bit-shift
    /// version of the extended Euclidean algorithm.
    ///
    /// #Description
    /// This function will also halve the value in an output
    /// register, modulo the `modulus`, exactly 2n-k times, 
    /// where k is the number of rounds in the EEA. 
    /// When uncomputing, it will double, which will correct
    /// the pseudo-inverse to a true inverse, and restore the 
    /// original value in the output register.
    ///
    /// # Inputs
    /// ## halveop
    /// An operation which is expected to halve
    /// the output value, modulo the modulus. This is 
    /// used to correct the pseudo-inverse.
    /// ## vs
    /// Qubit register containing the input (expected to
    /// be co-prime to the modulus or 0). This wll
    /// be set to the pseudo-inverse at the end of the computation.
    /// ## ancillas
    /// Ancilla qubits, assumed blank, that will be filled in this operation. 
    /// Requires 2 * n + floor(log n) + 2 qubits for an n-qubit input.
    ///
    /// # References
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///   Figure 9.
    operation _MontBitGCDWithAncillaInner(halveop : (Int => Unit is Ctl + Adj), vs : MontModInt, ancillas : Qubit[]) : Unit{
        body (...) {
            let modulus = vs::modulus;
            let nQubits=Length(vs::register!);
            let logn = BitSizeI(nQubits);
            AssertEnoughQubits(2 * nQubits + logn + 2, "Montgomery inverse ancilla: ", ancillas);
            /// Ancilla which records which branch of
            /// _MontBitGCDRound was executed in each round.
            let ms = ancillas[0 .. 2 * nQubits - 1];
            /// A SpecialCounter counting how many rounds have passed
            /// since the pseudo-inverse was found
            let counterQubits = ancillas[2 * nQubits .. 2 * nQubits + logn];
            /// A single qubit used as the top bit of the remainder, 
            /// which will have a value dependent on the input.
            let rCarry = ancillas[2 * nQubits + logn + 1];

            //Set up the counter
            let counter = QubitsAsCounter(counterQubits);
            counter::Prepare();
            using ((uQubits, rQubits, sQubits)=(Qubit[nQubits], Qubit[nQubits], Qubit[nQubits+1])){
                let vsLE = vs::register;
                let us = LittleEndian(uQubits);
                let rs = LittleEndian(rQubits + [rCarry]);
                let ss = LittleEndian(sQubits);
                //prep us, rs, ss
                ApplyXorInPlaceL(modulus, us);
                X(ss![0]);

                //If vs=0, the algorithm will immediately stop and just 
                //increment the counter for the full run.
                //To clear the ancilla, we need to immediately swap u and s
                //We use the top bit of rs to check
                //This allows the operation to function without error for
                //any input, including 0 (it will output "0" as an inverse)
                CheckIfAllZero(vsLE!, rs![nQubits]);
                (Controlled SwapLE)([rs![nQubits]], (us, LittleEndian(ss![0..nQubits - 1])));
                CheckIfAllZero(vsLE!, rs![nQubits]);
                //Run the rounds
                QuantumWhile(nQubits, 2 * nQubits, _MontBitGCDRound(_, us, vsLE, rs, ss, ms), CheckIfAllZero(vsLE!, _), halveop(_), counter);
                //Adjust r mod p 
                //This leaves the top bit of r in an unknown state
                (Adjoint AddConstant)(modulus, rs);
                (Controlled AddConstant)([rs![nQubits]], (modulus, LittleEndian(rs![0..nQubits - 1])));
                ModularNegConstantModulus(modulus, LittleEndian(rs![0..nQubits - 1]));
                //Swap rs into vs
                SwapLE(vsLE, LittleEndian(rs![0..nQubits - 1]));
                //Clear extra registers
                ApplyXorInPlaceL(modulus, ss);
                X(us![0]);
            }
        }
        controlled adjoint auto;
    }

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
    /// # Remarks
    /// `_MontBitGCDWithAncillaInner` has a very similar function, but
    /// produces only a "pseudo-inverse" of $x^{-1}2^{n-k}\mod m$, where
    /// $k$ is the number of rounds in the Euclidean algorithm. The missing powers
    /// of 2 can be added during the uncomputation; however, for this operation,
    /// we want the output to be the true inverse. Thus, it needs to directly 
    /// fix the pseudo-inverse.
    ///
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation ModularInvMontgomeryFormOpen(xs : MontModInt, ancillas : Qubit [], blankOutputs : MontModInt) : Unit {
        body (...){
            let nQubits = Length(xs::register!);
            let logn = BitSizeI(nQubits);
            let (nSelfAncilla, nSelfOutput) = AncillaCountModularInvMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Modular inversion ancilla: ", ancillas);
            AssertEnoughQubits(nSelfOutput, "Modular inversion outputs: ", blankOutputs::register!);
            let register = ancillas[0..2 * nQubits + logn + 1];
            let counterQubits = ancillas[2 * nQubits .. 2 * nQubits + logn];
            let counter = QubitsAsCounter(counterQubits);
            //Produces a pseudo-inverse
            _MontBitGCDWithAncillaInner(NoOp<Int>(_), xs, register);
            CopyMontModInt(xs,blankOutputs);
            //Corrects the pseudo-inverse
            using (secondCounterQubits = Qubit[logn + 1]){
                let secondCounter = QubitsAsCounter(secondCounterQubits);
                secondCounter::Prepare();
                let Decrementer = DummyIntegerWrapper((Adjoint counter::Increment), (), _);
                let DecrementAndHalve = ConcatenateOperations(Decrementer, ModularDblMontgomeryForm, _, blankOutputs);
                QuantumWhile(0, nQubits, DecrementAndHalve, OppositeCheck(counter::Test, _), NoOp<Int>(_), secondCounter);
                //Since counterQubits are in the zero state, we swap them out to uncompute.
                SwapLE(LittleEndian(counterQubits),LittleEndian(secondCounterQubits));
                (Adjoint secondCounter::Prepare)();
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Returns the number of ancilla and output qubits
    /// necessary for an open modular inverse
    /// in Montgomery form.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the integers being multiplied
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountModularInvMontgomeryForm (nQubits : Int) : (Int, Int) {
        let logn = BitSizeI(nQubits);
        return (2 * nQubits + logn + 2, nQubits);
    }

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
    /// # References
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remarks
    /// The overall action on the `outputs` register will be $2^k\circ copyop \circ 2^{-k} \mod m$
    /// where `modulus`$=m$. Hence, commuting with modular multiplication guarantees the expected
    /// behaviour, but if its the commutation relationship is known, it could be used 
    /// with non-commutative operations.
    operation InvertBitShiftConstantModulusGeneric(copyop : (MontModInt=> Unit is Ctl + Adj), doubleop : (Int=>Unit is Ctl + Adj), xs : MontModInt) : Unit {
        body (...) {
            (Controlled InvertBitShiftConstantModulusGeneric)(new Qubit[0], (copyop, doubleop, xs));
        }
        controlled (controls, ...){
            let modulus = xs::modulus;
            let nQubits=Length(xs::register!);
            let logn = BitSizeI(nQubits);
            using (register =Qubit[2 * nQubits + logn + 2]){
                
                //Not controlled because it will be reversed immediately
                 _MontBitGCDWithAncillaInner(doubleop(_), xs, register);
                //Here we want to copy r out
                //Note : We expect copyop to copy into `outputs`, since that is what gets doubled
                // appropriately to fix `xs`.
                (Controlled copyop)(controls, (xs));
                //Uncompute
                (Adjoint _MontBitGCDWithAncillaInner)(doubleop(_), xs, register);
            }
        }
        controlled adjoint auto;
    }


}