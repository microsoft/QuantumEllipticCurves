// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Arithmetic {
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Crypto.Basics;

    open Microsoft.Quantum.ModularArithmetic.DebugHelpers ;

    ////////////////////////////////////////////////////////////////////////////////////////////
    ///////                                                                             ////////
    ///////                          BASIC ARITHMETIC                                   ////////
    ///////                                                                             ////////
    ////////////////////////////////////////////////////////////////////////////////////////////


    //////////////////////      WRAPPERS      //////////////////////


    /// # Summary
    /// Carries out a strictly greater than comparison of two integers x
    /// and y encoded in quantum registers. If x>y, then the
    /// result qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer $x$.
    /// ## ys
    /// Qubit register encoding the second integer $y$
    /// ## carry
    /// Single qubit that will be flipped if $x>y$.
    operation GreaterThanWrapper(xs : LittleEndian, ys : LittleEndian, result : Qubit) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()){
                GreaterThanLookAhead(xs, ys, result);
            } elif (IsMinimizeTCostMetric()){
                CKDMGGreaterThan(xs, ys, result);
            } else {
                GreaterThan(xs, ys, result);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Carries out a strictly greater than comparison of a an integer x
    /// encoded in a qubit register against a constant integer$c. If x>c, then the
    /// result qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## constant
    /// Constant c.
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## carry
    /// Single qubit that will be flipped if x>c.
    operation GreaterThanConstant(constant : BigInt, xs : LittleEndian, result : Qubit) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()) {
                GreaterThanConstantLookAhead(constant, xs, result);
            } elif (IsMinimizeTCostMetric()) {
                CompareToConstant(true, CKDMGGreaterThan, constant, xs, result);
            } else {
                CompareToConstant(true, GreaterThan, constant, xs, result);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Carries out a strictly less than comparison of a an integer x
    /// encoded in a qubit register against a constant integer c. If x<c, then the
    /// result qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## constant
    /// BigInt constant $c$.
    /// ## xs
    /// LittleEndian qubit register encoding the integer $x$
    /// ## carry
    /// Single qubit that will be flipped if $x<c$.
    operation LessThanConstant(constant : BigInt, xs : LittleEndian, result : Qubit) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()) {
                LessThanConstantLookAhead(constant, xs, result);
            } elif (IsMinimizeTCostMetric()) {
                CompareToConstant(false, CKDMGGreaterThan, constant, xs, result);
            } else {
                CompareToConstant(false, GreaterThan, constant, xs, result);
            }
            //
            
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place adder with carry. Given two n-bit integers
    /// `xs` and `ys` encoded in qubit Registers and a
    /// qubit carry, computes the sum of the two
    /// integers where the n least significant bits of the 
    /// result are held in `ys` and the carry out is xored to the
    /// qubit `carry`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, modified to hold the n least significant bits of
    /// the sum.
    /// ## carry
    /// Carry qubit, xored with the most significant bit of the sum.
    operation AddInteger(xs : LittleEndian, ys : LittleEndian, carry : Qubit) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()) {
                CarryLookAheadAdder(xs, ys, carry);	
            } elif (IsMinimizeTCostMetric()) {
                CDKMGAdder(xs, ys, carry);	
            } else {
                RippleCarryAdderTTK(xs, ys, carry);
            }							
        }
        // controlled (controls, ...){
        // 	//(Controlled CarryLookAheadAdder)(controls, (xs, ys, carry));	//low depth
        // 	//(Controlled RippleCarryAdderTTK(xs, ys, carry));				//low width
        // }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place adder with no carry. Given two n-bit integers
    /// `xs` and `ys` encoded in qubit registers and a
    /// qubit carry, computes the sum of the two
    /// integers modulo 2^n, where the result is held in `ys`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, modified to hold the n least significant bits of
    /// the sum.
    operation AddIntegerNoCarry(xs : LittleEndian, ys : LittleEndian) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()) {
                CarryLookAheadAdderNoCarry(xs, ys);
            } elif (IsMinimizeTCostMetric()) {
                CDKMGAdderNoCarry(xs, ys);
            } else {
                RippleCarryAdderNoCarryTTK(xs, ys);
            }
        }
        // controlled (controls, ...){
        // 	(Controlled CarryLookAheadAdderNoCarry)(controls, (xs, ys));
        // }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer x encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry-out, i.e. x + constant mod 2^n, 
    /// where n is the length of `xs`.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer $x$.
    ///
    /// # Remarks
    /// Uses one of three internal versions, optimized for width, depth, or T-count.
    /// Currently uses the depth-optimized version.
    operation AddConstant (constant : BigInt, xs : LittleEndian) : Unit
    {
        body (...) {
            if (IsMinimizeDepthCostMetric()) {
                CarryLookAheadAddConstant(constant, xs);
            } elif (IsMinimizeTCostMetric()) {
                CDKMGAddConstant(constant, xs);
            } else {
                _AddConstantLowWidth(constant, xs);
            }
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }

    ////////////// End of wrappers /////////////

    /// # Summary
    /// Swaps two little-endian registers of the same length.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register.
    /// ## ys
    /// Qubit register.
    ///
    /// # Remarks
    /// For n-qubit inputs, the controlled version allocates n ancillas
    /// to fan-out the controls and achieve log(n) depth.
    operation SwapLE(xs : LittleEndian, ys : LittleEndian) : Unit {
        body (...){
            Fact(Length(xs!) == Length(ys!), $"Registers must have equal lengths to swap (current lengths : {Length(xs!)} and {Length(ys!)})");
            for (idx in 0..Length(xs!) - 1){
                SWAP(xs![idx], ys![idx]);
            }
        }
        controlled(controls, ...){
            Fact(Length(xs!) == Length(ys!), $"Registers must have equal lengths to swap (current lengths : {Length(xs!)} and {Length(ys!)})");
            if (IsMinimizeWidthCostMetric()) {
                for (idx in 0 .. Length(xs!) - 1){
                    (Controlled SWAP)(controls, (xs![idx], ys![idx]));
                }
            } else {
                using (singleControls = Qubit[Length(xs!)]){
                    (Controlled FanoutControls)(controls, (singleControls));
                    for (idx in 0..Length(xs!) - 1){
                        (Controlled SWAP)([singleControls[idx]], (xs![idx], ys![idx]));
                    }
                    (Adjoint Controlled FanoutControls)(controls, (singleControls));
                }
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Bit-wise XOR the value in `inputs` into `outputs.
    ///
    /// # Inputs
    /// ## inputs
    /// Qubit register of inputs
    /// ## outputs
    /// Qubit register that `inputs` will be XORed against
    operation CopyLittleEndian(inputs : LittleEndian, outputs : LittleEndian) : Unit{
        body(...){
            Fact(Length(inputs!)==Length(outputs!), 
                $"Inputs should be the same length; they are {Length(inputs!)} and {Length(outputs!)}"
            );
            for (idx in 0..Length(inputs!)-1){
                CNOT(inputs![idx], outputs![idx]);
            }
        }
        controlled (controls,...){
            Fact(Length(inputs!)==Length(outputs!), 
                $"Inputs should be the same length; they are {Length(inputs!)} and {Length(outputs!)}"
            );
            if (IsMinimizeWidthCostMetric()) {
                for (idx in 0 .. Length(inputs!) - 1){
                    (Controlled X)(controls + [inputs![idx]], (outputs![idx]));
                }
            } else {
                using (singleControls = Qubit[Length(inputs!)]){
                    (Controlled FanoutControls)(controls, (singleControls));
                    for (idx in 0..Length(inputs!) - 1){
                        (Controlled X)([singleControls[idx],inputs![idx]], (outputs![idx]));
                    }
                    (Adjoint Controlled FanoutControls)(controls, (singleControls));
                }
            }
        }
        adjoint controlled auto;
    }
    



    /// # Summary
    /// ApplyXorInPlace for BigInt.
    /// Applies X operations to qubits in a LittleEndian register
    /// based on the 1 bits in an integer.
    ///
    /// # Input
    /// ## value
    /// Big integer which is assumed to be non-negative
    /// ## target
    /// Quantum register which is used to store value in LittleEndian encoding
    ///
    /// # Remarks
    /// The controlled version fans out the control to ancillas, using 
    /// as many ancilla as the number of ones in `value`.
    operation ApplyXorInPlaceL (value : BigInt, target : LittleEndian) : Unit {
        body (...) {
            let valArray = BigIntAsBoolArray(value);
            if (Length(valArray) > Length(target!)){
                for (idxVal in Length(target!)..Length(valArray) - 1){
                    Fact(not valArray[idxVal], $"Cannot XOR {value} into a {Length(target!)}-bit register; the number is too big");
                }
            }
            for (idxVal in 0..Length(valArray) - 1){
                if (valArray[idxVal]){
                    X(target![idxVal]);
                }
            }
        }
        controlled (controls, ...){
            let posArray = PositionsOfOnesInBigInt(value);
            if (Length(posArray)>0){//if the length is zero, then value=0
                Fact(posArray[Length(posArray) - 1] < Length(target!), $"Cannot XOR {value} into a {Length(target!)}-bit register; the number is too big");
                if (IsMinimizeWidthCostMetric()) {
                    for (idx in 0 .. Length(posArray) - 1) {
                        (Controlled X)(controls, (target![posArray[idx]]));
                    }
                } else { // not low depth
                    using (singleControls = Qubit[Length(posArray)]){
                        (Controlled FanoutControls)(controls, (singleControls));
                        for (idx in 0..Length(posArray) - 1){
                            CNOT(singleControls[idx], target![posArray[idx]]);
                        } 
                        (Adjoint Controlled FanoutControls)(controls, (singleControls));
                    }
                }
            }
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Returns an integer array, where each integer points 
    /// to the positions of a 1 in the little-endian binary
    /// representation of the input integer.
    ///
    /// # Inputs
    /// ## value
    /// BigInt integer
    function PositionsOfOnesInBigInt(value : BigInt) : Int[] {
        mutable positionArray = new Int[HammingWeightL(value)];
        mutable idxPos=0;
        mutable idxVal = 0;
        mutable internalValue = value;
        while (internalValue > 0L){
            if (internalValue % 2L == 1L){
                set positionArray w/= idxPos <- idxVal;
                set idxPos = idxPos + 1;
                set internalValue = internalValue-1L;
            }
            set idxVal = idxVal + 1;
            set internalValue = internalValue/2L;
        }
        return positionArray;
    }

    /// # Summary
    /// Measures the content of a quantum register and converts
    /// it to an integer. The measurement is performed with respect
    /// to the standard computational basis, i.e., the eigenbasis of PauliZ.
    ///
    /// # Input
    /// ## target
    /// A quantum register in the little-endian encoding.
    ///
    /// # Output
    /// ## BigInt
    /// An unsigned BigInt that contains the measured value of `target`
    ///
    /// # Remarks
    /// This operation resets its input register to the all-zeros
    /// state, suitable for releasing back to a target machine.
    operation MeasureBigInteger(target : LittleEndian) : BigInt {
        let targetAsBoolArray= ResultArrayAsBoolArray(MultiM(target!));
        mutable measuredBigInt = 0L;
        for (idxB in Length(targetAsBoolArray)-1..(-1)..0){
            set measuredBigInt=2L * measuredBigInt;
            if (targetAsBoolArray[idxB]){
                set measuredBigInt = measuredBigInt + 1L;
            }
        }
        ResetAll(target!);
        return measuredBigInt;
    }

    /// # Summary
    /// Reversible, in-place increment operation. Given an integer $x$ encoded 
    /// in the LittleEndian qubit register `xs`, this operation adds the constant $1$ 
    /// to the integer. The result is computed without carry-out, i.e. the operation
    /// computes x + 1 mod 2^n, where n is the length of the register `xs`.
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Craig Gidney : Constructing large increment gates, Blog post, 2015
    ///   http : //algassert.com/circuits/2015/06/12/Constructing-Large-Increment-Gates.html
    ///
    /// # Remarks
    /// The operation requires n dirty ancilla qubits that are borrowed and returned 
    /// in the same state they are received.
    operation Increment (xs : LittleEndian) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);

            borrowing (g = Qubit[nQubits]) {
                let gs = LittleEndian(g);

                if ( nQubits > 3) {
                    (Adjoint AddIntegerNoCarry) (gs, xs);
                    ApplyToEachWrapperCA(X, gs!);
                    (Adjoint AddIntegerNoCarry) (gs, xs);
                    ApplyToEachWrapperCA(X, gs!);
                } elif (nQubits == 3) {
                    CCNOTWrapper (xs![0], xs![1], xs![2]);
                    CNOT (xs![0], xs![1]);
                    X (xs![0]);
                } elif (nQubits == 2) {
                    CNOT (xs![0], xs![1]);
                    X (xs![0]);
                } elif (nQubits == 1) {
                    X (xs![0]);
                }
            }
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }

    /// # Summary
    /// Forward operation to compute the carry when adding an integer constant
    /// to an integer x encoded in a qubit register.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## gs
    /// Qubit register of dirty qubits, are returned in the same state as received.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// This operation is used in the ComputeCarry operation below together with its adjoint
    /// to compute the carry and uncompute the corresponding addition. It explicitly takes a
    /// qubit register of dirty qubits as input. 
    operation _ComputeCarryCascade (constant : BigInt, xs : LittleEndian, gs : LittleEndian) : Unit
    { 
        body (...) {
            (Controlled _ComputeCarryCascade) (new Qubit[0], (constant, xs, gs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            let constantbittemp = BigIntAsBoolArray(constant);
            let bitextension = MaxI(nQubits-Length(constantbittemp), 1);
            let constantbits = constantbittemp + new Bool[bitextension];
            for (idx in (nQubits-1)..(-1)..2) {
                if (constantbits[idx]) {
                    (Controlled CNOT) (controls, (xs![idx], gs![idx-1]));
                    (Controlled X) (controls, (xs![idx]));
                }
                CCNOTWrapper (gs![idx-2], xs![idx], gs![idx-1]);
            }
            if (constantbits[1]) {
                (Controlled CNOT) (controls, (xs![1], gs![0]));
            }
            if (constantbits[0]) {
                if (constantbits[1]) {
                    (Controlled X) (controls, (xs![1]));
                }
                (Controlled CCNOTWrapper) (controls, (xs![0], xs![1], gs![0]));
            }

            for (idx in 1..(nQubits-2)) {
                CCNOTWrapper (gs![idx-1], xs![idx + 1], gs![idx]);
            }
        }
        adjoint controlled auto;
    }
    


    /// # Summary
    /// Computes the carry when adding the integer constant given in the first argument to the
    /// integer x encoded in the qubit register `xs`, using borrowed qubits.
    /// 
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// The specified control operation uses symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation ComputeCarry (constant : BigInt, xs : LittleEndian, carry : Qubit) : Unit
    {
        body (...) {
            (Controlled ComputeCarry) (new Qubit[0], (constant, xs, carry));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);
    
            if (nQubits == 1) {
                if ((constant % 2L) == 1L) {
                    (Controlled CNOT) (controls, (xs![0], carry));
                }
            } else {
                borrowing (gs = Qubit[nQubits-1]) {
                    (Controlled CNOT) (controls, (gs[nQubits - 2], carry));
                    _ComputeCarryCascade(constant, xs, LittleEndian(gs));
                    (Controlled CNOT) (controls, (gs[nQubits - 2], carry));
                    (Adjoint _ComputeCarryCascade) (constant, xs, 
                                                    LittleEndian(gs));
                }
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Recursive operation to compute carries in the AddConstant operation below.
    /// Uses a divide-and-conquer approach to recursively compute the carries on one 
    /// half of the qubits while using the other half as dirty ancilla qubits.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// The specified control operation makes use of symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation _CarryAndDivide (constant : BigInt, xs : LittleEndian) : Unit
    {
        body (...) {
            (Controlled _CarryAndDivide) (new Qubit[0], (constant, xs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);

            if (nQubits > 1) {
                let lengthLower = nQubits - nQubits/2;
                let lengthHigher = nQubits - lengthLower;
                let xsLower = LittleEndian(xs![0..(lengthLower-1)]);
                let xsHigher = LittleEndian(xs![lengthLower..(nQubits-1)]);
                let constantLower = constant % 2L ^ lengthLower;
                let constantHigher = constant / 2L ^ lengthLower;

                borrowing (gs = Qubit[1]) {
                    Increment(LittleEndian([gs[0]] + xsHigher!));
                    X(gs[0]);

                    ApplyToEachWrapperCA(CNOT(gs[0], _), xsHigher!);

                    (Controlled ComputeCarry)(controls, (constantLower, xsLower, gs[0]));

                    Increment(LittleEndian([gs[0]] + xsHigher!));
                    X(gs[0]);

                    (Controlled ComputeCarry)(controls, (constantLower, xsLower, gs[0]));

                    ApplyToEachWrapperCA(CNOT(gs[0], _), xsHigher!);
                }
                (Controlled _CarryAndDivide)(controls, (constantLower, xsLower));
                (Controlled _CarryAndDivide)(controls, (constantHigher, xsHigher));
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reversible, in-place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer x encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry-out, i.e. x + constant mod 2^n, 
    /// where n is the length of `xs`.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    operation _AddConstantLowWidth (constant : BigInt, xs : LittleEndian) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);
            _CarryAndDivide(constant, xs);
            ApplyXorInPlaceL(constant, xs);
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }




    /// # Summary
    /// Reversible, in-place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer $x$ encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry-out, i.e. x + constant mod 2^n, 
    /// where n is the length of `xs`.
    /// 
    /// Compared to  `AddConstantLowWidth`, this has lower depth by a factor of log n, but uses
    /// an extra n qubits.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    operation _AddConstantLowT(constant : BigInt, xs : LittleEndian) : Unit {
        body (...) {
            (Controlled _AddConstantLowT)(new Qubit[0], (constant, xs));
        }
        controlled (controls, ...){
            let nQubits = Length(xs!);
            using (constantQubits = Qubit[nQubits]){
                let constants = LittleEndian(constantQubits);
                (Controlled ApplyXorInPlaceL)(controls, (constant, constants));
                AddIntegerNoCarry(constants, xs);
                (Controlled ApplyXorInPlaceL)(controls, (constant, constants));
            }
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Reversible, in-place adder with carry, that uses 
    /// a linear depth circuit, n ancilla qubits, and 
    /// 4n T gates.
    ///
    /// # Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers where the n least significant bits of the 
    /// result are held in `ys` and the carry out is xored to the
    /// qubit `carry`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the $n$ least significant bits of
    /// the sum.
    /// ## carry
    /// Carry qubit, is xored with the most significant bit of the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderD, 
    /// RippleCarryAdderCDKM, and RippleCarryAdderTTK.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CDKMGAdder (xs : LittleEndian, ys : LittleEndian, carry : Qubit) : Unit {
        body (...){
            _CDKMGAdderInner(true, xs, ys, [carry]);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place adder without carry, that uses 
    /// a linear depth circuit, n ancilla qubits, and 
    /// 4n T gates.
    ///
    /// # Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers, modulo 2^n, where the n least significant bits of the 
    /// result are held in `ys`
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the $n$ least significant bits of
    /// the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderNoCarryD, 
    /// RippleCarryAdderNoCarryCDKM, and RippleCarryAdderNoCarryTTK.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CDKMGAdderNoCarry (xs : LittleEndian, ys : LittleEndian) : Unit {
        body (...){
            _CDKMGAdderInner(false, xs, ys, new Qubit[0]);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place adder for a quantum register
    /// and a classical constant, that uses 
    /// a linear depth circuit, n ancilla qubits, and 
    /// less than 4n T gates.
    ///
    /// # Description
    /// Given two n-bit integers, one
    /// encoded in a LittleEndian Registers `xs` and the other
    /// as a classical BigInt, the operation computes the sum of the two
    /// integers modulo 2^n, where the result is written over `xs`
    ///
    /// # Inputs
    /// ## constant
    /// The classical integer summand
    /// ## xs
    /// Qubit register encoding the quantum integer summand.
    ///
    /// # Remarks
    /// The method here is to allocate ancilla qubits to store
    /// the constant, control writing the constant in, and then
    /// do an uncontrolled addition.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CDKMGAddConstant (constant : BigInt, xs : LittleEndian) : Unit {
        body (...){
            (Controlled CDKMGAddConstant)(new Qubit[0], (constant, xs));
        }
        controlled (controls, ...){
            let nQubits = Length(xs!);
            Fact(nQubits>=BitSizeL(constant), $"{constant} is too big to add to a {nQubits} - qubit register");
            using (constantQubits = Qubit[nQubits]){
                let constants = LittleEndian(constantQubits);
                (Controlled ApplyXorInPlaceL)(controls, (constant, constants));
                _CDKMGAdderInner(false, constants, xs, new Qubit[0]);
                (Controlled Adjoint ApplyXorInPlaceL)(controls, (constant, constants));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes a single "block" of addition for the CDKM-Gidney
    /// adder. Takes one bit from each summand and the previous carry,
    /// correctly computes the next carry, and XORs the previous carry
    /// with the bits of the summands.
    ///
    /// # Inputs
    /// ## previousCarry
    /// The previous carry qubit 
    /// ## xQubit
    /// The qubit of the summand that is not overwritten
    /// ## yQubit
    /// The qubit of the summand which is overwritten with the sum
    /// ## nextCarry
    /// The next carry qubit
    ///
    /// # Remarks
    /// `_CDKMGBlockBackward` is almost the inverse of `_CDKMGBlockForward`, except
    /// the backward block will alter the yQubit. However, if they are controlled by 0, then 
    /// they are inverses of each other. This saves in controlled operations, but makes both
    /// operations ill-defined when controlled by 0.
    ///
    /// # References
    /// Figure 2 from Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGBlockForward (previousCarry : Qubit, xQubit : Qubit, yQubit : Qubit, nextCarry : Qubit) : Unit {
        body (...){
            (Controlled _CDKMGBlockForward)(new Qubit[0], (previousCarry, xQubit, yQubit, nextCarry));
        }
        controlled (controls, ...){
            CNOT(previousCarry, xQubit);
            (Controlled CNOT)(controls, (previousCarry, yQubit));
            AndWrapper(xQubit, yQubit, nextCarry);
            CNOT(previousCarry, nextCarry);
        }
        controlled adjoint auto;

    }

    /// # Summary
    /// Computes a single backward "block" of addition for the CDKM-Gidney
    /// adder. Uncomputes the next carry qubit, restores the qubit 
    /// from the first summand to its initial value, and writes the 
    /// correct sum value to the the qubit of the second summand.
    ///
    /// # Inputs
    /// ## previousCarry
    /// The previous carry qubit 
    /// ## xQubit
    /// The qubit of the summand that is not overwritten
    /// ## yQubit
    /// The qubit of the summand which is overwritten with the sum
    /// ## nextCarry
    /// The next carry qubit
    ///
    /// # Remarks
    /// `_CDKMGBlockBackward` is almost the inverse of `_CDKMGBlockForward`, except
    /// the backward block will alter the yQubit. However, if they are controlled by 0, then 
    /// they are inverses of each other. This saves in controlled operations, but makes both
    /// operations ill-defined when controlled by 0.
    ///
    /// # References
    /// Figure 2 from Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGBlockBackward (previousCarry : Qubit, xQubit : Qubit, yQubit : Qubit, nextCarry : Qubit) : Unit {
        body (...){
            (Controlled _CDKMGBlockBackward)(new Qubit[0], (previousCarry, xQubit, yQubit, nextCarry));
        }
        controlled (controls, ...){
            CNOT(previousCarry, nextCarry);
            (Adjoint AndWrapper)(xQubit, yQubit, nextCarry);
            CNOT(previousCarry, xQubit);
            (Controlled CNOT)(controls, (xQubit, yQubit));
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Generic operation used for addition with or without carry.
    /// Adds two quantum integers in-place.
    //
    // # Inputs
    /// ## useCarry
    /// If true, the operation will copy out the carry bit.
    /// ## xs
    /// The first quantun integer summand
    /// ## ys
    /// The second quantum integer summand, to be overwritten with the sum.
    /// ## carry
    /// Qubit array for the carry qubit. Should be either length 0 (if useCarry is false)
    /// or length 1 (if useCarry is true).
    ///
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGAdderInner(useCarry : Bool, xs : LittleEndian, ys : LittleEndian, carry : Qubit[]) : Unit {
        body (...) {
            (Controlled _CDKMGAdderInner)(new Qubit[0], (useCarry, xs, ys, carry));
        }
        controlled (controls, ...) {
            if (useCarry){
                Fact(Length(carry) == 1, $"Expected 1 carry qubit but got {Length(carry)}");
            } else {
                Fact(Length(carry) == 0, $"Expected 0 carry qubits but got {Length(carry)}");
            }
            let nQubits = Length(xs!);
            Fact(nQubits == Length(ys!), $"Qubit registers must have the same size to add");
            if (nQubits == 1){// special case
                if (useCarry){
                    (Controlled RippleCarryAdderTTK)(controls, (xs, ys, carry[0]));
                } else {
                    (Controlled RippleCarryAdderNoCarryTTK)(controls, (xs, ys));
                }
            }
            else {
                using (carries = Qubit[nQubits]){
                    AndWrapper(xs![0], ys![0], carries[0]);
                    for (idx in 1..nQubits - 1){
                        (Controlled _CDKMGBlockForward)(controls, (carries[idx - 1], xs![idx], ys![idx], carries[idx]));
                    }
                    if (useCarry){
                        (Controlled CNOT)(controls, (carries[nQubits - 1], carry[0]));
                    }
                    for (idx in (nQubits - 1)..(-1)..1){
                        (Controlled _CDKMGBlockBackward)(controls, (carries[idx - 1], xs![idx], ys![idx], carries[idx]));
                    }
                    (Adjoint AndWrapper)(xs![0], ys![0], carries[0]);
                    (Controlled CNOT)(controls, (xs![0], ys![0]));
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Carries out a strictly greater than comparison of two integers x
    /// and y, encoded in qubit registers xs and ys. If x>y, then the
    /// restult qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y
    /// ## carry
    /// Single qubit that will be flipped if x>y.
    ///
    /// # Remarks
    /// This operation has the same functionality as GreaterThan.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CKDMGGreaterThan (xs : LittleEndian, ys : LittleEndian, carry : Qubit) : Unit {
        body (...){
            _CDKMGCompareInner(xs, ys, carry);
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Uses a quantum comparator to compare
    /// a quantum integer to a constant by
    /// writing the constant into an ancilla register
    /// 
    operation CompareToConstant (
        isGreaterThan : Bool,
        Comparator : ((LittleEndian, LittleEndian, Qubit) => Unit is Ctl + Adj),
        constant : BigInt, 
        xs : LittleEndian, 
        carry : Qubit 
    ) : Unit {
        body (...) {
            (Controlled CompareToConstant)(new Qubit[0], (isGreaterThan, Comparator, constant, xs, carry));
        }
        controlled (controls, ...){
            let nQubits = Length(xs!);
            using (constantQubits = Qubit[nQubits]){
                let constants = LittleEndian(constantQubits);
                if (isGreaterThan){
                    ApplyToEachWrapperCA(X, constantQubits);
                    (Controlled ApplyXorInPlaceL)(controls, (2L^nQubits - 1L - constant, constants));
                    Comparator(xs, constants, carry);
                    (Controlled Adjoint ApplyXorInPlaceL)(controls, (2L^nQubits - 1L - constant, constants));
                    (Adjoint ApplyToEachWrapperCA)(X, constantQubits);
                } else {
                    (Controlled ApplyXorInPlaceL)(controls, (constant, constants));
                    Comparator(constants, xs, carry);
                    (Controlled Adjoint ApplyXorInPlaceL)(controls, (constant, constants));
                }
                
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Internal function to compare two quantum integers, 
    /// flipping the carry qubit if and only if the first integer
    /// is greater than the second
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y
    /// ## carry
    /// Single qubit that will be flipped if x>y.
    ///
    /// # Remarks
    /// This operation has the same functionality as GreaterThan.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGCompareInner (xs : LittleEndian, ys : LittleEndian, carry : Qubit) : Unit {
    body (...) {
            (Controlled _CDKMGCompareInner)(new Qubit[0], (xs, ys, carry));
        }
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            if (nQubits == 1){
                X(ys![0]);
                (Controlled AndWrapper)(controls, (xs![0], ys![0], carry));
                X(ys![0]);
            } else {
                ApplyToEachCA(X, ys!);
                using (carries = Qubit[nQubits]){
                    AndWrapper(xs![0], ys![0], carries[0]);
                    for (idx in 1..nQubits - 1){
                        _CDKMGBlockForward (carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                    }
                    (Controlled CNOT)(controls, (carries[nQubits - 1], carry));
                    for (idx in (nQubits - 1)..(-1)..1){
                        (Adjoint _CDKMGBlockForward)(carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                    }
                    (Adjoint AndWrapper)(xs![0], ys![0], carries[0]);
                }
                ApplyToEachCA(Adjoint X, ys!);
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Reversible, in-place adder with carry, that uses 
    /// a logarithmic depth carry look-ahead circuit with
    /// 2n - o(n) ancilla qubits. 
    ///
    /// # Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers where the n least significant bits of the 
    /// result are held in `ys` and the carry out is xored to the
    /// qubit `carry`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the $n$ least significant bits of
    /// the sum.
    /// ## carry
    /// Carry qubit, is xored with the most significant bit of the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderD, 
    /// RippleCarryAdderCDKM, and RippleCarryAdderTTK, but uses ancilla qubits
    /// and has logarithmic depth.
    ///
    /// If `ys` has more qubits than `xs`, the adder would simply ignore the leading
    /// bits of `ys`. Since this is likely undesired behaviour, the operation
    /// instead throws an exception if they are not the same size.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic-Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    operation CarryLookAheadAdder(xs : LittleEndian, ys : LittleEndian, carry : Qubit) : Unit {
        body (...){
            //Odd bit-lengths are much less expensive so we add an extra qubit
            // and do everything as an even bit-length addition
            if (Length(xs!) % 2 == 0){
                using (bonusQubits = Qubit[1]){
                    _CLAAdderImpl(CNOT, CCNOTWrapper, AndWrapper, false, xs! + [bonusQubits[0]], ys! + [carry], new Qubit[0]);
                }
            } else {
                _CLAAdderImpl(CNOT, CCNOTWrapper, AndWrapper, true, xs!, ys!,  [carry]);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place adder with no carry, that uses 
    /// a logarithmic depth carry look-ahead circuit with
    /// 2n - o(n) ancilla qubits. 
    ///
    /// #Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers modulo 2^n, where the result is held in `ys`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the n least significant bits of
    /// the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderNoCarryD, 
    /// RippleCarryAdderNoCarryCDKM, and RippleCarryAdderNoCarryTTK, but uses 
    /// ancilla qubits and has logarithmic depth.
    ///
    /// If `ys` has more qubits than `xs`, the adder would simply ignore the leading
    /// bits of `ys`. Since this is likely undesired behaviour, the operation
    /// instead throws an exception if they are not the same size.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic - Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    operation CarryLookAheadAdderNoCarry(xs : LittleEndian, ys : LittleEndian) : Unit {
        body(...){
            _CLAAdderImpl(CNOT, CCNOTWrapper, AndWrapper, false, xs!, ys!, new Qubit[0]);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in - place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer $x$ encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry - out, i.e. $x + constant \mod 2 ^ n$, 
    /// where $n$ is the length of `xs`.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// LittleEndian qubit register encoding the integer $x$.
    ///
    /// # Remarks
    /// This has the same function as _AddConstantLowT and _AddConstantLowWidth
    /// but this has logarithmic depth and 2n - o(n) ancilla.
    operation CarryLookAheadAddConstant(constant : BigInt, xs : LittleEndian) : Unit {
        body(...){
            let nQubits = Length(xs!);
            Fact(nQubits>=BitSizeL(constant), $"{constant} is too big to add to a {nQubits} - qubit register");
            let constantArray = BigIntAsBoolArray(constant) + new Bool[nQubits - BitSizeL(constant)];
            _CLAAdderImpl(
                ClassicalCNOT, 
                ClassicalCCNOT, 
                ClassicalAND, 
                false, 
                constantArray[0.. nQubits - 1], 
                xs!, 
                new Qubit[0]
            );
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Internal function for carry-look ahead adding. 
    /// Adds a classical or quantum input
    /// to a quantum input, using a carry
    /// if `useCarry` is true.
    ///
    /// # Inputs
    /// ## cqCNOT
    /// Acts like a CNOT, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CNOT; if it is a Bool, then its a conditional
    /// X gate
    /// ## cqCCNOTWrapper
    /// Acts like a CCNOTWrapper, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CCNOTWrapper; if it is a Bool, then its a conditional
    /// CNOT gate (between the remaining Qubit inputs)
    /// ## cqAND
    /// The same action as cqCCNOTWrapper, but we can use a function
    /// optimized for the case where we are guaranteed that the
    /// target qubit starts in the 0 state.
    /// ## useCarry
    /// Determines whether the function uses a carry (if true)
    /// or does not use a carry (addition mod 2^n) (if false)
    /// ## xs
    /// Array of the first integer to be added (classical or quantum)
    /// ## ys 
    /// Qubit register of the second integer to be added (to contain 
    /// output)
    /// ## carry
    /// Single qubit for the carry (if `useCarry` is true) or 
    /// length-0 qubit array (if `useCarry` is false). Other lengths
    /// will cause errors
    operation _CLAAdderImpl <'T> (
        cqCNOT : (('T, Qubit) => Unit is Ctl + Adj),
        cqCCNOTWrapper : (('T, Qubit, Qubit) => Unit is Ctl + Adj),
        cqAND : (('T, Qubit, Qubit) => Unit is Ctl + Adj),
        useCarry : Bool, 
        xs : 'T[], 
        ys : Qubit[], 
        carry : Qubit[]
    ) : Unit {
        body(...){
            (Controlled _CLAAdderImpl)(new Qubit[0], (cqCNOT,cqCCNOTWrapper, cqAND, useCarry, xs, ys, carry));
        }
        controlled(controls, ...){
            //Control logic : The circuit can be split into 5 steps : 
            // 1) Prepare the initial carries
            // 2) Compute all carries
            // 3) Compute the sum
            // 4) Uncompute the carries
            // 5) Uncompute the initial carries
            //
            // We only need to control step 3, since the others
            // will uncompute themselves.
            // However : The uncompute steps don't apply
            // every operation to the first and last qubits, 
            // so those operations are controlled.
            let nQubits = Length(xs);
            
            Fact(nQubits == Length(ys), $"Qubit registers must have the same length to add;
                first has length {Length(xs)} and second has length {Length(ys)}");

            if (useCarry){
                Fact(Length(carry) == 1, $"Carry lookahead adder can only use one carry;
                    {Length(carry)} qubits given");
            } else {
                Fact(Length(carry) == 0, $"Carry lookahead adder must have zero-length
                    carry array for no-carry addition");
            }

            if (nQubits==1){// special case
                if (useCarry){
                    (Controlled cqCCNOTWrapper)(controls, (xs[0], ys[0], carry[0]));
                }
                (Controlled cqCNOT)(controls, (xs[0], ys[0]));
            } else {
                let logn = Floor(Lg(IntAsDouble(nQubits)));
                let ancillaSize = 2 * nQubits - HammingWeightI(nQubits) - logn;
                using (ancillaQubits = Qubit[ancillaSize]){
                    let gens = ancillaQubits[0..nQubits - 2] + carry;
                    let propArrays = PropArrays(ancillaQubits[nQubits - 1..ancillaSize - 1], ys);
                    // 1) Compute initial carries
                
                    cqAND(xs[0], ys[0], gens[0]);
                    (Controlled cqCNOT)(controls, (xs[0], ys[0]));//will not be uncomputed
                    for (idx in 1..nQubits - 2){
                        cqAND(xs[idx], ys[idx], gens[idx]);
                        cqCNOT(xs[idx], ys[idx]);
                    }
                    if (useCarry){
                        (Controlled cqCCNOTWrapper)(controls, (xs[nQubits - 1], ys[nQubits -1], gens[nQubits - 1]));//will not be uncomputed
                    }
                    (Controlled cqCNOT)(controls, (xs[nQubits - 1], ys[nQubits -1]));//will not be uncomputed

                    // 2) Compute all carries
                    if (useCarry){
                        (Controlled _LookAheadAndComputePropagateCarries)(controls, (nQubits, propArrays));
                        (Controlled _LookAheadAndComputeGenerateCarries)(controls, (nQubits, propArrays, gens));
                        (Controlled _LookAheadTurnCarriesIntoSum)(controls, (nQubits, propArrays, gens));
                        (Adjoint Controlled _LookAheadAndComputePropagateCarries)(controls, (nQubits, propArrays));
                    } else {
                        _LookAheadAndComputePropagateCarries(nQubits - 1, propArrays);
                        _LookAheadAndComputeGenerateCarries(nQubits - 1, propArrays, gens);
                        _LookAheadTurnCarriesIntoSum(nQubits - 1, propArrays, gens);
                        (Adjoint _LookAheadAndComputePropagateCarries)(nQubits - 1, propArrays);
                    }
                    // 3) Compute the sum
                    // If it's controlled, it needs to fanout
                    /// into ancilla to keep the depth low
                    if (Length(controls)>0){
                        using (singleControls = Qubit[nQubits - 1]){
                            (Controlled FanoutControls)(controls, (singleControls));
                            CNOT(singleControls[0], ys[0]);
                            CCNOTWrapper(singleControls[0], gens[0], ys[1]);
                            for (ids in 1..nQubits - 2){
                                CCNOTWrapper(singleControls[ids], gens[ids], ys[ids + 1]);
                                CNOT(singleControls[ids], ys[ids]);
                                cqCCNOTWrapper(xs[ids], singleControls[ids], ys[ids]);
                            }
                            (Adjoint Controlled FanoutControls)(controls, (singleControls));
                        }
                    } else {//without controls
                        X(ys[0]);
                        CNOT(gens[0], ys[1]);
                        for (ids in 1..nQubits - 2){
                            CNOT(gens[ids], ys[ids + 1]);
                            X(ys[ids]);
                            cqCNOT(xs[ids], ys[ids]);
                        }
                    }

                    // 4) Uncompute all carries
                     _LookAheadAndComputePropagateCarries(nQubits - 1, propArrays);
                    (Adjoint _LookAheadTurnCarriesIntoSum)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputeGenerateCarries)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputePropagateCarries)(nQubits - 1, propArrays);

                    // 5) Uncompute initial carries
                    (Adjoint cqAND)(xs[0], ys[0], gens[0]);
                    for (ids in 1..nQubits - 2){
                        cqCNOT(xs[ids], ys[ids]);
                        (Adjoint cqAND)(xs[ids], ys[ids], gens[ids]);
                    }
                        
                    //This final negation had no inverse in step (1)
                    (Controlled ApplyToEachWrapperCA)(controls, (X, ys[0..nQubits - 2]));
                }
            }
        }
        controlled adjoint auto;
    }





    /// # Summary
    /// Carries out a strictly greater than comparison of two integers x
    /// and y, encoded in qubit registers xs and ys. If x>y, then the
    /// restult qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y
    /// ## carry
    /// Single qubit that will be flipped if x>y.
    ///
    /// # Remarks
    /// This operation has the same functionality as GreaterThan.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic - Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    /// This does not implement the comparator described in the reference, 
    /// but simply alters the addition circuit to only output the carry.
    operation GreaterThanLookAhead(xs : LittleEndian, ys : LittleEndian, carry : Qubit) : Unit {
        body (...){
            (Controlled GreaterThanLookAhead)(new Qubit[0], (xs, ys, carry));
        }
        controlled (controls, ...){
            if (Length(xs!) % 2 == 0){
                using (bonusQubits = Qubit[2]){		
                    (Controlled GreaterThanLookAhead)(controls, (
                        LittleEndian(xs! + [bonusQubits[0]]),
                        LittleEndian(ys! + [bonusQubits[1]]),
                        carry)
                    );
                }
            } else {
                ApplyToEachWrapperCA(X, ys!);
                (Controlled _CompareLookAheadImpl)(controls,  (
                    CNOT,
                    CCNOTWrapper,
                    AndWrapper,
                    xs!, 
                    ys!, 
                    carry
                ));
                ApplyToEachWrapperCA(X, ys!);
            }
        }
        controlled adjoint auto;
    }


    

    

    /// # Summary
    /// Carries out a strictly greater than comparison of a an integer x
    /// encoded in a qubit register against a constant integer c. If x>c, then the
    /// result qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## constant
    /// Classical constant c.
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## carry
    /// Single qubit that will be flipped if x>c.
    ///
    /// # Remarks
    /// This operation has a similar struction to GreaterThanLookahead, 
    /// but with a reduced number of controlled gates.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic - Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    /// This does not implement the comparator described in the reference, 
    /// but simply alters the addition circuit to only output the carry.
    operation GreaterThanConstantLookAhead(constant : BigInt, xs : LittleEndian, carry : Qubit) : Unit {
        body (...){
            let nQubits = Length(xs!);
            if (constant >= 2L^nQubits - 1L){
                //Since xs <= 2^nQubits -1, in this case the constant
                // must be greater, so we do not clip the carry
            } else {
                let constantComplement = constant ^^^ 2L^nQubits - 1L;
                let constantArray = BigIntAsBoolArray(constantComplement) + new Bool[nQubits - BitSizeL(constantComplement)];
                _CompareLookAheadImpl(
                    ClassicalCNOT,
                    ClassicalCCNOT,
                    ClassicalAND,
                    constantArray[0..nQubits - 1],
                    xs!,
                    carry
                );
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Carries out a strictly greater than comparison of a constant integer c
    /// against an integer x encoded in a qubit register. If c<x, then the
    /// result qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## constant
    /// Classical constant c.
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## carry
    /// Single qubit that will be flipped if c<x.
    ///
    /// # Remarks
    /// This operation has a similar struction to GreaterThanLookahead, 
    /// but with a reduced number of controlled gates.
    /// Uses the trick that x - y=(x' + y)', where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic - Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    /// This does not implement the comparator described in the reference, 
    /// but simply alters the addition circuit to only output the carry.
    operation LessThanConstantLookAhead(constant : BigInt, xs : LittleEndian, carry : Qubit) : Unit{
        body (...){
            (Controlled LessThanConstantLookAhead)(new Qubit[0], (constant, xs, carry));
        }
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            if (constant > 2L^nQubits - 1L){
                //Since xs <= 2^nQubits -1, in this case the constant
                // must be greater, so we fip the carry without any work
                (Controlled X)(controls, (carry));
            } else {
                let constantArray = BigIntAsBoolArray(constant) + new Bool[nQubits - BitSizeL(constant)];
                ApplyToEachWrapperCA(X, xs!);
                (Controlled _CompareLookAheadImpl)(controls,  (
                    ClassicalCNOT,
                    ClassicalCCNOT,
                    ClassicalAND,
                    constantArray[0.. nQubits -1], 
                    xs!, 
                    carry
                ));
                ApplyToEachWrapperCA(X, xs!);
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Computes the only the carry of the sum of
    /// a quantum/classical integer and a quantum integer.
    /// Used internally for comparators.
    ///
    /// # Inputs
    /// ## cqCNOT
    /// Acts like a CNOT, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CNOT; if it is a Bool, then its a conditional
    /// X gate
    /// ## cqCCNOTWrapper
    /// Acts like a CCNOTWrapper, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CCNOTWrapper; if it is a Bool, then its a conditional
    /// CNOT gate (between the remaining Qubit inputs)
    /// ## cqAND
    /// The same action as cqCCNOTWrapper, but we can use a function
    /// optimized for the case where we are guaranteed that the
    /// target qubit starts in the 0 state.
    /// ## xs
    /// Array of the first integer to be compared (classical or quantum)
    /// Assumed to be already complemented (all bits flipped)
    /// ## ys 
    /// Qubit register of the second integer to be compared (to contain 
    /// output)
    /// ## carry
    /// Single qubit for the carry; flipped if the 
    /// second input is strictly greater than the first
    ///
    /// # Remarks
    /// The comparators use the fact that (c' + x)'=x-c
    /// to the comparison; this circuit asssumes that 
    /// `xs` is already complemented.
    operation _CompareLookAheadImpl<'T>(
        cqCNOT : (('T, Qubit) => Unit is Ctl + Adj),
        cqCCNOTWrapper : (('T, Qubit, Qubit) => Unit is Ctl + Adj),
        cqAND : (('T, Qubit, Qubit) => Unit is Ctl + Adj),
        xs : 'T[], //pre-complemented
        ys : Qubit[], 
        carry : Qubit
    ) : Unit {
        body(...){
            (Controlled _CompareLookAheadImpl)(new Qubit[0], (
                cqCNOT,
                cqCCNOTWrapper,
                cqAND,
                xs, 
                ys, 
                carry
            ));
        }
        controlled(controls, ...){
            let nQubits = Length(xs);
            if (nQubits==1){//edge case
                (Controlled cqCCNOTWrapper)(controls, (xs[0], ys[0], carry));
            } else {
                let logn = Floor(Lg(IntAsDouble(nQubits)));
                let ancillaSize = 2 * nQubits - Floor(Lg(IntAsDouble(nQubits - 1))) - 3;

                using (ancillaQubits = Qubit[ancillaSize]){
                    let gens = ancillaQubits[0..nQubits - 2] + [carry];
                    let propArrays = PropArrays(ancillaQubits[nQubits - 1..ancillaSize - 1], ys);
                

                    // 1) Compute initial carries
                    for (idx in 0..nQubits - 2){
                        cqAND(xs[idx], ys[idx], gens[idx]);
                        cqCNOT(xs[idx], ys[idx]);			
                    }
                    (Controlled cqCCNOTWrapper)(controls, (xs[nQubits - 1], ys[nQubits - 1], gens[nQubits - 1]));//will not be uncomputed
                    cqCNOT(xs[nQubits - 1], ys[nQubits - 1]);

                    // 2) Compute all carries
                    _LookAheadAndComputePropagateCarries(nQubits, propArrays);
                    (Controlled _LookAheadAndComputeGenerateCarries)(controls, (nQubits, propArrays, gens));
                    (Controlled _LookAheadTurnCarriesIntoSum)(controls, (nQubits, propArrays, gens));
                    (Adjoint _LookAheadTurnCarriesIntoSum)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputeGenerateCarries)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputePropagateCarries)(nQubits, propArrays);

                     
                    // 5) Uncompute initial carries
                    for (ids in 0..nQubits - 2){	
                        cqCNOT(xs[ids], ys[ids]);
                        (Adjoint cqAND)(xs[ids], ys[ids], gens[ids]);
                    }
                    cqCNOT(xs[nQubits - 1], ys[nQubits - 1]);
                }
            }
        }
        controlled adjoint auto;
    }



    /// # Summary
    /// Divides an array of qubits into a two-dimensional array
    /// necessary for running a lookahead carry addition.
    /// Since the indexing is complicated, rather than
    /// compute it directly, it simply iterates over all
    /// carry propagation bits and sequential assigns them
    /// a bit in the input array.
    ///
    /// # Inputs
    /// ## props
    /// A blank qubit array to be reassigned.
    /// ## ys
    /// A qubit array expected to contain P_0, the 0th level
    /// of carry propagation qubits
    ///
    /// # Outputs
    /// A two-dimensional qubit array such that Proparrays[t][x] corresponds
    /// to the xth element in level t, where t ranges from 0 to 
    /// Floor(log n) - 1 and x ranges from 1 to Floor(n/2^t)-1.
    /// Note that Proparrays[0][x] references elements of ysarray.
    /// 
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation prepares the set of arrays P as described in
    ///    Section 3.
    function PropArrays(props : Qubit[], ys : Qubit[]) : Qubit[][] {
        let nQubits = Length(ys);
        let logn = Floor(Lg(IntAsDouble(nQubits)));
        mutable propArrays = new Qubit[][logn];
        mutable idxProps=0;
        set propArrays w/= 0 <- ys;
        for (level in 1..logn - 1){
            let levelSize = nQubits/2^level - 1;
            mutable levelProps = new Qubit[levelSize + 1];
            for (idm in 1..levelSize){
                set levelProps w/= idm <- props[idxProps];
                set idxProps = idxProps + 1;
            }
            set propArrays w/= level <- levelProps;
        }
        return propArrays;
    }

/// # Summary
    /// Given carry propagation bits for sequential elements, 
    /// this computes the rest of the carry propagation bits.
    /// 
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits to carry on (which can be
    /// less than the number of qubits in gens)
    /// ## propArrays
    /// A two-dimensional array referencing different levels of
    /// carry propagation qubits (intended to be the output of
    /// PropArrays), with the 0th level computed.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation computes step 1 from Section 3.
    ///		(the blue gates in Figure 5)
    operation _LookAheadAndComputePropagateCarries(nQubits : Int, propArrays : Qubit[][]) : Unit {
        body (...){
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            for (idxRound in 1..logn-1){
                for (idxProps in 1..nQubits / (2 ^ idxRound) - 1){
                        AndWrapper(propArrays[idxRound - 1][2 * idxProps], propArrays[idxRound - 1][2 * idxProps + 1], propArrays[idxRound][idxProps]);
                }
            }
        }
        controlled (controls, ...){
        //The full adder must uncompute these carries at the end, 
        //so we save controls by not controlling this operation.
        //However : When uncomputing, the adder only calls
        //this operation with nQubits-1. Thus, we must
        //control the individual operations that use
        //qubits in the n-1 position.
        //Hence, each of the "rounds" must check whether the
        //indices are high enough to need the controls.
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            // P rounds
            for (idxRound in 1..logn - 1){
                let lognMin1 = Floor(Lg(IntAsDouble(nQubits - 1)));
                for (idxProps in 1..nQubits / (2 ^ idxRound) - 1){
                    if (idxRound > lognMin1 - 1 or idxProps > (nQubits - 1) / (2 ^ idxRound) - 1){
                        (Controlled X)(controls + propArrays[idxRound-1][2 * idxProps..2 * idxProps + 1], (propArrays[idxRound][idxProps]));
                    } else {
                        AndWrapper(propArrays[idxRound - 1][2 * idxProps], propArrays[idxRound - 1][2 * idxProps + 1], propArrays[idxRound][idxProps]);
                    }
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Given carry propagation bits and carry generations for
    /// sequential elements, this computes the rest of the
    /// generator carries.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits to carry on (which can be
    /// less than the number of qubits in gens)
    /// ## propArrays
    /// A two-dimensional array referencing different levels of
    /// carry propagation qubits, pre-computed.
    /// ## gens 
    /// A qubit array of the carry generation qubits, 
    /// initialized with the sequential elements.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation computes steps 2 from Section 3.
    ///		(the red gates in Figure 5)
    operation _LookAheadAndComputeGenerateCarries(nQubits : Int, propArrays : Qubit[][], gens : Qubit[]) : Unit {
        body (...){
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            for (idxRound in 1..logn){
                for (idxGens in 0..(nQubits / 2 ^ idxRound) - 1){
                    CCNOTWrapper(propArrays[idxRound - 1][2 * idxGens + 1], 
                        gens[idxGens * 2 ^ idxRound + 2 ^ (idxRound - 1) - 1],
                        gens[(idxGens + 1) * 2 ^ idxRound - 1]
                    );
                }
            }
        }
        controlled (controls, ...){
            //The full adder must uncompute these carries at the end, 
            //so we save controls by not controlling this operation.
            //However : When uncomputing, the adder only calls
            //this operation with nQubits-1. Thus, we must
            //control the individual operations that use
            //qubits in the n-1 position.
            //Hence, each of the "rounds" must check whether the
            //indices are high enough to need the controls.
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            for (idxRound in 1..logn){
                let lognmin1 = Floor(Lg(IntAsDouble(nQubits - 1)));
                for (idxGens in 0..(nQubits / 2 ^ idxRound) - 1){
                    if (idxRound > lognmin1 or idxGens > (nQubits - 1)/(2 ^ idxRound) - 1){
                        (Controlled X)(controls + [propArrays[idxRound - 1][2 * idxGens + 1],
                            gens[idxGens * (2 ^ idxRound) + 2 ^ (idxRound - 1) - 1]], 
                            (gens[(idxGens + 1) * 2 ^ idxRound - 1])
                        );
                    }  else {
                        CCNOTWrapper(propArrays[idxRound - 1][2 * idxGens + 1], 
                            gens[idxGens * (2 ^ idxRound) + 2^(idxRound - 1) - 1],
                            gens[(idxGens + 1) * (2 ^ idxRound) - 1]
                        );
                    }
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Given pre-computed carry propagation bits and carry 
    /// generation bits, this computes the carries for the sum
    /// of two integers.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits to carry on (which can be
    /// less than the number of qubits in gens)
    /// ## propArrays
    /// A two-dimensional array referencing different levels of
    /// carry propagation qubits, fully computed.
    /// ## gens
    /// A qubit array of the carry generation qubits.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation computes step 3 from Section 3.
    ///	(the green parts of the circuit in Figure 5)
    operation _LookAheadTurnCarriesIntoSum(nQubits : Int, propArrays : Qubit[][], gens : Qubit[]) : Unit {
        body (...){
            let log2nover3 = Floor(Lg(2.0 * IntAsDouble(nQubits) / 3.0));
            for (idxRound in log2nover3..(-1)..1){
                for (idxSum in 1.. (nQubits - 2 ^ (idxRound - 1)) / 2 ^ idxRound){
                        CCNOTWrapper(gens[idxSum * (2 ^ idxRound) - 1], 
                            propArrays[idxRound - 1][2 * idxSum],
                            gens[idxSum * (2 ^ idxRound) + 2 ^ (idxRound - 1) - 1]
                        );
                }
            }
        }
        controlled (controls, ...){
            //The full adder must uncompute these carries at the end, 
            //so we save controls by not controlling this operation.
            //However : When uncomputing, the adder only calls
            //this operation with nQubits-1. Thus, we must
            //control the individual operations that use
            //qubits in the n-1 position.
            //Hence, each of the "rounds" must check whether the
            //indices are high enough to need the controls.
            let log2nover3 = Floor(Lg(2.0 * IntAsDouble(nQubits) / 3.0));	
            for (idxRound in log2nover3..( - 1)..1){
                let log2nmin1over3 = Floor(Lg(2.0 * IntAsDouble(nQubits - 1) / 3.0));
                for (idc in 1.. (nQubits - 2 ^ (idxRound - 1)) / 2 ^ idxRound){
                    if (idxRound > log2nmin1over3 or idc > (nQubits - 1 - 2 ^ (idxRound - 1)) / 2 ^ idxRound){
                        (Controlled X)(controls + 
                            [gens[idc * 2 ^ idxRound - 1], propArrays[idxRound - 1][2 * idc]],
                            (gens[idc * 2 ^ idxRound + 2 ^ (idxRound - 1) - 1])
                        );
                    } else {
                        CCNOTWrapper(gens[idc * 2 ^ idxRound - 1], 
                            propArrays[idxRound - 1][2 * idc], 
                            gens[idc * 2 ^ idxRound + 2 ^ (idxRound - 1) - 1]
                        );
                    }
                }
            }
        }
        controlled adjoint auto;
    }
}