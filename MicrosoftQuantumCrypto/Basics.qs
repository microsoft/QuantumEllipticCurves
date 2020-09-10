// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Basics {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Random;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Crypto.Arithmetic;


    ////////////////////////////////////////////////////////////////////////////////////////////
    ///////                                                                             ////////
    ///////                                BASIC OPS                                    ////////
    ///////                                                                             ////////
    ////////////////////////////////////////////////////////////////////////////////////////////

    function IsTestable () : Bool {
        body intrinsic;
    }

    function IsMinimizeDepthCostMetric () : Bool {
        body intrinsic;
	}

    function IsMinimizeTCostMetric () : Bool {
        body intrinsic;
	}

    function IsMinimizeWidthCostMetric () : Bool {
        body intrinsic;
	}

    ///////////// Wrappers ///////////

    /// # Summary
    /// Applies a single-qubit operation to each element in a register. 
    /// Wrapper to choose different operations depending on the cost metric.
    operation ApplyToEachWrapperCA<'T>(singleElementOperation : ('T => Unit is Ctl + Adj), register : 'T[]) : Unit {
        body (...){
            if (IsMinimizeWidthCostMetric()){
                ApplyToEachCA(singleElementOperation, register);
            } else {
                ApplyToEachLowDepthCA(singleElementOperation, register);
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Applies the doubly-controlled NOT (CCNOT) gate
    /// to three qubits. Wrapper for alternative CCNOT
    /// circuits.
    ///
    /// # Inputs
    /// ## control1
    /// The first control qubit
    /// ## control2		
    /// The second control qubit
    /// ## target
    /// The output qubit 
    operation CCNOTWrapper(control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...){
            if (IsTestable()){
                CCNOT(control1, control2, target);
            } else {
                if (IsMinimizeWidthCostMetric()){
                    ccnot_T_depth_3(control1, control2, target);
                } else {
                    ccnot_T_depth_1(control1, control2, target);
                }
            }
        }
        controlled (controls, ...){
            CheckIfAllOnes(controls + [control1, control2], target);
        }
        controlled adjoint auto;
    }

    //------Low-T circuits-----//

    // /// # Summary
    // /// CCNOT gate over the Clifford+T gate set, in T-depth 1, according to Selinger
    // /// # Remarks
    // ///
    // /// # References
    // /// - [ *P. Selinger*,
    // ///        Phys. Rev. A 87: 042302 (2013)](http://doi.org/10.1103/PhysRevA.87.042302)
    // /// # See Also
    // /// - For the circuit diagram see Figure 1 on
    // ///   [ Page 3 of arXiv:1210.0974v2 ](https://arxiv.org/pdf/1210.0974v2.pdf#page=2)
    operation ccnot_T_depth_1 (control1 : Qubit, control2 : Qubit, target : Qubit) : Unit is Adj + Ctl {
        using (auxillaryRegister = Qubit[4]) {

            // apply UVU† where U is outer circuit and V is inner circuit
            ApplyWithCA(TDepthOneCCNOTOuterCircuit, TDepthOneCCNOTInnerCircuit, auxillaryRegister + [target, control1, control2]);
        }
    }


    /// # See Also
    /// - Used as a part of @"Microsoft.Quantum.Samples.UnitTesting.TDepthOneCCNOT"
    /// - For the circuit diagram see Figure 1 on
    ///   [ Page 3 of arXiv:1210.0974v2 ](https://arxiv.org/pdf/1210.0974v2.pdf#page=2)
    operation TDepthOneCCNOTOuterCircuit (qs : Qubit[]) : Unit is Adj + Ctl {
        EqualityFactI(Length(qs), 7, "7 qubits are expected");
        H(qs[4]);
        CNOT(qs[5], qs[1]);
        CNOT(qs[6], qs[3]);
        CNOT(qs[5], qs[2]);
        CNOT(qs[4], qs[1]);
        CNOT(qs[3], qs[0]);
        CNOT(qs[6], qs[2]);
        CNOT(qs[4], qs[0]);
        CNOT(qs[1], qs[3]);
    }

    operation ccnot_T_depth_3 (control1 : Qubit, control2 : Qubit, target : Qubit) : Unit is Adj {
        body (...){
            H(target);
            T(control2);
            T(control1);
            T(target);
            CNOT(control2, control1);
            CNOT(target,control2);
            CNOT(control1,target);
            (Adjoint T)(control2);
            CNOT(control1, control2);
            (Adjoint T)(control1);
            (Adjoint T)(control2);
            T(target);
            CNOT(target, control2);
            CNOT(control1, target);
            CNOT(control2, control1);
            H(target);
        }
    }


    /// # See Also
    /// - Used as a part of @"Microsoft.Quantum.Samples.UnitTesting.TDepthOneCCNOT"
    /// - For the circuit diagram see Figure 1 on
    ///   [ Page 3 of arXiv:1210.0974v2 ](https://arxiv.org/pdf/1210.0974v2.pdf#page=2)
    operation TDepthOneCCNOTInnerCircuit (qs : Qubit[]) : Unit is Adj + Ctl {
        EqualityFactI(Length(qs), 7, "7 qubits are expected");
        ApplyToEachCA(Adjoint T, qs[0 .. 2]);
        ApplyToEachCA(T, qs[3 .. 6]);
    }

    /// # Summary
    /// Computes the logical AND of two qubit inputs, 
    /// setting a target qubit to the result. The target
    /// qubit must be initialized to 0.
    ///
    /// # Inputs
    /// ## control1
    /// The first bit in the AND
    /// ## control2
    /// The second bit in the AND
    /// ## target
    /// The output qubit which must be 0
    ///
    /// # Remarks
    /// This has the same action as CCNOTWrapper when the target is 0.
    /// This function is a wrapper that may use circuits optimized 
    /// for AND, rather than a general CCNOTWrapper.
    operation AndWrapper(control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()){
                ApplyLowDepthAnd(control1, control2, target);
            } else {
                ApplyAnd(control1, control2, target);
            }
        }
        controlled (controls, ...){
            (Controlled CCNOTWrapper)(controls, (control1, control2, target));
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Sequential QRAM look-up, where a qubit register storing an 
    /// address controls which element of a classical array is written 
    /// to a quantum registers
    ///
    /// # Description
    /// Sequentially iterates through all addresses, compares the address to 
    /// the address register, and if they are equal, it writes the value from the 
    /// classical array to a quantum register. The type of the classical array,
    /// and the action within the classical array are left unspecified. The quantum
    /// register is implicit in the `QuantumWrite` operation.
    ///
    /// Bits in the table beyond the range of address are ignored.
    /// It is assumed that the address will never store a value beyond the end of the table.
    /// Invalid addresses cause undefined behavior.
    ///
    /// # Input
    /// ## table
    /// The classical table whose values will be indexed and written into the target register.
    /// ## QuantumWrite
    /// A controllable operation which will write a specific value to some quantum register. 
    /// This could be an in-place XOR, for example.
    /// ## address
    /// Determines which integer from the table will be xored into the target.
    /// 
    /// # References
    /// Much of this code is directly adapted from the following reference, with slight
    /// modifications to fit with the rest of the Microsoft.Quantum.Crypto library:
    /// Craig Gidney. 2019. "Windowed Quantum Arithmetic", https://arxiv.org/abs/1905.07682
    operation EqualLookup<'T> (table: 'T[], QuantumWrite : (('T) => Unit is Ctl + Adj), address: LittleEndian) : Unit {
        body (...) {
            Controlled EqualLookup(new Qubit[0], (table, QuantumWrite, address));
        }
        controlled (cs, ...) {
            if (Length(table) == 0) {
                fail "Can't lookup values in an empty table.";
            }
            // Compress controls: we only want a single control at one time
            if (Length(cs) > 1){
                using (controlQubit = Qubit()){
                    CheckIfAllOnes(cs, controlQubit);
                    (Controlled EqualLookup)([controlQubit], (table, QuantumWrite, address));
                    (Adjoint CheckIfAllOnes)(cs, controlQubit);
                }
            } else {

                // Drop high bits that would place us beyond the range of the table.
                let maxAddressLen = BitSizeI(Length(table));
                if (maxAddressLen < Length(address!)) {
                    let kept = LittleEndian(address![0..maxAddressLen - 1]);
                    (Controlled EqualLookup)(cs, (table, QuantumWrite, kept));
                } else {

                    // Drop inaccessible parts of table.
                    let maxTableLen = 1 <<< Length(address!);
                    if (maxTableLen < Length(table)) {
                        let kept = table[0..maxTableLen-1];
                        (Controlled EqualLookup)(cs, (kept, QuantumWrite, address));
                    } elif (Length(table) == 1) {

                        // Base case: singleton table.
                        ApplyToEachWrapperCA(X, address!);
                        (Controlled QuantumWrite)(cs + address!, (table[0]));
                        ApplyToEachWrapperCA(Adjoint X, address!);
                    } else {

                        // Recursive case: divide and conquer.
                        let highBit = address![Length(address!) - 1];
                        let restAddress = LittleEndian(address![0..Length(address!) - 2]);
                        let h = 1 <<< (Length(address!) - 1);
                        let lowTable = table[0..h-1];
                        let highTable = table[h..Length(table)-1];
                        using (q = Qubit()) {
                            // Store 'all(controls) and not highBit' in q.
                            X(highBit);
                            if (Length(cs) > 0){
                                 AndWrapper(cs[0], highBit, q);
                            } else {
                                CNOT(highBit, q);
                            }
                            X(highBit);

                            // Do lookup for half of table where highBit is 0.
                            (Controlled EqualLookup)([q], (lowTable, QuantumWrite, restAddress));

                            // Flip q to storing 'all(controls) and highBit'.
                            if (Length(cs) > 0){
                                CNOT(cs[0], q);
                            } else {
                                X(q);
                            }

                            // Do lookup for half of table where highBit is 1.
                            (Controlled EqualLookup)([q], (highTable, QuantumWrite, restAddress));

                            // Eager uncompute 'q = all(controls) and highBit'.
                            if (Length(cs) > 0){
                                 (Adjoint AndWrapper)(cs[0], highBit, q);
                            } else {
                                CNOT(highBit, q);
                            }
                        }
                    }
                }
            }
        }
        adjoint (...) {
            (Controlled EqualLookup)(new Qubit[0], (table, (Adjoint QuantumWrite), address));
        }
        controlled adjoint (controls, ...){
            (Controlled EqualLookup)(controls, (table, (Adjoint QuantumWrite), address));
        }
    }

    /// # Summary
    /// Acts like a CCNOTWrapper, but with one input classical.
    /// It flips the target if the logical AND
    /// of the first two inputs is 1.
    ///
    /// # Inputs
    /// ## control1
    /// Classical bit input
    /// ## control2
    /// Qubit input
    /// ## target
    /// Qubit output
    operation ClassicalCCNOT(control1 : Bool, control2 : Qubit, target : Qubit) : Unit {
        body (...){
            if (control1){
                CNOT(control2, target);
            }
        }
        controlled (controls, ...){
            if (control1){
                (Controlled CNOT)(controls, (control2, target));
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Acts like a CNOT, but with one input classical.
    /// It flips the target if the first input is true.
    ///
    /// # Inputs
    /// ## control1
    /// Classical bit input
    /// ## target
    /// Qubit output
    operation ClassicalCNOT(control : Bool, target : Qubit) : Unit {
        body (...){
            if (control) {
                X(target);
            }
        }
        controlled (controls, ...){
            if (control) {
                (Controlled X)(controls, (target));
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Acts like an AND, but with one input classical.
    /// It flips the target if the logical AND
    /// of the first two inputs is 1. Assumes the
    /// target starts in the 0 state.
    ///
    /// # Inputs
    /// ## control1
    /// Classical bit input
    /// ## control2
    /// Qubit input
    /// ## target
    /// Qubit output
    operation ClassicalAND(control1 : Bool, control2 : Qubit, target : Qubit) : Unit {
        body (...){
            if (control1){
                CNOT(control2, target);
            }
        }
        controlled (controls, ...){
            if (control1){
                (Controlled CNOT)(controls, (control2, target));
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Splits an array into an array of disjoint, evenly-sized
    /// pieces of the original array.
    ///
    /// # Inputs
    /// ## array
    /// Array of objects
    /// ## size
    /// The size of subarrays that will be returned
    ///
    /// # Outputs
    /// ## 'T[][]
    /// An array of disjoint subarrays of `array`
    ///
    /// # Remarks
    /// The length of `array` must be evenly divisible by `size`.
    function EvenlyPartitionedArray<'T>(array : 'T[], size : Int) : 'T[][] {
        let length = Length(array);
        let nPartitions = length/size;
        Fact((Length(array) % size) == 0, $"Cannot evenly partition array of length
            {Length(array)} into pieces of size {size}.");
        mutable returnArray = new 'T[][nPartitions];
        for (idx in 0.. nPartitions - 1){
            set returnArray w/= idx <- array[size * idx .. size * (idx + 1) - 1];
        }
        return returnArray;
    }

    /// # Returns a (nearly uniform) randomly
    /// sampled big integer less than a specified value.
    ///
    /// # Inputs
    /// ## size
    /// Maximum size, so the returned value is between
    /// 0 and size-1 inclusive.
    ///
    /// # Outputs
    /// ## BigInt
    /// Random integer
    operation RandomBigInt(size : BigInt) : BigInt {
        mutable randomBigInt = 0L;
        let nBits = 2 * BitSizeL(size);
        let maxInt = Min([nBits, 32]);
        for (idx  in 0..nBits/maxInt-1){
            set randomBigInt = (2L^maxInt) * randomBigInt + IntAsBigInt(DrawRandomInt(0,2^maxInt-1));
        }
        return randomBigInt % size;
    }

    /// # Returns a (nearly uniform) randomly
    /// sampled big integer in a specific interval.
    ///
    /// # Inputs
    /// ## lowerBound
    /// Minimum size: Returned value is at least this large.
    /// ## upperBound
    /// Maximum size: Returned value is strictly smaller
    /// than this value.
    ///
    /// # Outputs
    /// ## BigInt
    /// Random integer
    operation RandomBoundedBigInt(lowerBound : BigInt, upperBound : BigInt) : BigInt {
        Fact(lowerBound < upperBound, $"Lower bound {lowerBound} must be larger than upper bound {upperBound}");
        return lowerBound + RandomBigInt(upperBound - lowerBound);
    }

    /// # Summary
    /// Tests the size of a qubit register and causes an exception 
    /// if it does not fit a specified size.
    ///
    /// # Description
    /// Given a number of qubits as input, tests if a qubit array has at least that
    /// many qubits. If not, it throws an error. 
    /// If the qubit array has too many qubits, it instead sends a message, but does not
    /// halt the program.
    ///
    /// # Inputs
    /// ## qubitsRequired
    /// The number of qubits needed in the qubit array.
    /// ## message
    /// A message that is prepended to the error and warning messages,
    /// to indicate which function causes this error.
    /// ## qubitInputs
    /// The qubit array whose length is being tested.
    function AssertEnoughQubits(qubitsRequired : Int, message : String, qubitInputs : Qubit[]) : Unit {
        Fact(qubitsRequired <= Length(qubitInputs),
            message + $"Need {qubitsRequired} qubits, only given {Length(qubitInputs)}");
        if (qubitsRequired < Length(qubitInputs)){
            Message(message + $" warning: needed {qubitsRequired} qubits, given {Length(qubitInputs)}");
        }
    }

    /// # Summary
    /// Wraps a function such that it takes an integer as input,
    /// which it will then ignore. Intended for use with `QuantumWhile`.
    ///
    /// # Description
    /// The `QuantumWhile` function takes operations of the form
    /// (Int => Unit is Ctl + Adj) as arguments. However, certain uses
    /// of a quantum while loop use operations that do not take integer arguments
    /// (i.e., the same operation is applied in every iteration). 
    /// To fit the shape that `QuantumWhile` expects, we need to add a dummy integer
    /// variable to such an operation.
    ///
    /// # Inputs
    /// ## op
    /// The operation we want to add the integer argument to.
    /// ## inputs
    /// Any inputs that will be curried into the operation. 
    /// ## dummyInt
    /// The unused integer that `QuantumWhile` looks for.
    ///
    /// # Example
    /// Suppose we wanted to repeatedly add an integer `xs` to another `ys`.
    /// That is, we want to call `AddInteger(xs,ys)`. We would instead write:
    /// `let newOp = DummyIntegerWrapper(AddInteger,(xs,ys),_);`
    /// Then any time we call `newOp(n)`, for any integer `n`, it will call
    /// `AddInteger(xs,ys)`.
    operation DummyIntegerWrapper<'T>(op : ('T => Unit is Ctl + Adj), inputs: 'T, dummyInt : Int) : Unit {
        body (...){
            op(inputs);
        } 
        controlled (controls,...){
            (Controlled op)(controls, (inputs));
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Takes two operations and their inputs and applies both.
    /// Intended to be partially applied and used as an operator argument.
    ///
    /// # Inputs
    /// ## firstOp
    /// One operation to run
    /// ## secondPp
    /// A second operation to run
    /// ## firstInputs
    /// Inputs that are passed to the first operation
    /// ## secondInputs
    /// Inputs that are passed to the second operation
    operation ConcatenateOperations<'T1,'T2>(firstOp : ('T1 => Unit is Ctl + Adj), secondOp : ('T2 => Unit is Ctl + Adj), firstInputs : 'T1, secondInputs : 'T2 ) : Unit {
        body (...){
            firstOp(firstInputs);
            secondOp(secondInputs);
        }
        controlled (controls,...){
            using (innerControl = Qubit()){
                (Controlled X)(controls, (innerControl));
                (Controlled firstOp)(controls, (firstInputs));
                (Controlled secondOp)([innerControl], (secondInputs));
                (Controlled X)(controls, (innerControl));
            }
        }
        adjoint auto;
    }

    /// # Summary
    /// Computes the Hamming weight of a big integer.
    ///
    /// # Inputs
    /// ## value
    /// Big integer to compute Hamming weight.
    /// 
    /// # Output
    /// ## Int
    /// The Hamming weight of the big integer.
    function HammingWeightL(value : BigInt) : Int {
        let valArray = BigIntAsBoolArray(value);
        mutable valHamWeight = 0;
        for (idxVal in 0..Length(valArray)-1){
            if (valArray[idxVal]){
                set valHamWeight = valHamWeight+1;
            }
        }
        return valHamWeight;
    }

    /// # Summary
    /// Computes the Hamming weight of an integer.
    ///
    /// # Inputs
    /// ## value
    /// Integer to compute Hamming weight.
    /// 
    /// # Output
    /// ## Int
    /// The Hamming weight of the integer.
    function HammingWeightI(value : Int) : Int {
        let valArray = IntAsBoolArray(value, BitSizeI(value));
        mutable valHamWeight = 0;
        for (idxVal in 0..Length(valArray)-1){
            if (valArray[idxVal]){
                set valHamWeight = valHamWeight+1;
            }
        }
        return valHamWeight;
    }

    /// # Summary
    /// Applies a single qubit operation to 
    /// every qubit in an array.
    ///
    /// # Inputs
    /// ## op
    /// The operation to be applied.
    /// ## qubitArray
    /// The qubit array to which `op` is applied.
    ///
    /// # Remarks
    /// The function is identical to ApplyToEachWrapperCA
    /// but has a higher width and lower depth when controlled, 
    /// thanks to a fanout tree.
    operation ApplyToEachLowDepthCA<'T>(op : ('T => Unit is Ctl + Adj), qubitArray : 'T[]) : Unit {
        body(...){
            ApplyToEachCA(op, qubitArray);
        }
        controlled (controls, ...){
            let nQubits=Length(qubitArray);
            using (singleControls = Qubit[nQubits]){
                (Controlled X)(controls, singleControls[0]);
                FanoutToZero(singleControls[0], singleControls[1..nQubits - 1]);
                for (idx in 0..nQubits - 1){
                    (Controlled op)([singleControls[idx]], (qubitArray[idx]));
                }
                (Adjoint FanoutToZero)(singleControls[0], singleControls[1..nQubits - 1]);
                (Controlled X)(controls, singleControls[0]);
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Rotates a register `xs` of qubits in place by shifting all qubits from the least
    /// significant towards the most significant qubit by one step, placing the
    /// most significant qubit into the least significant postion : 
    /// `(xs[0], xs[1], ..., xs[nQubits-1]) -> (xs[nQubits-1], xs[0], ..., xs[nQubits-2])`
    ///
    /// # Input
    /// ## xs
    /// Qubit register, is replaced with its rotation.
    ///
    /// # Remarks
    /// If the register `xs` encodes an integer, this operation computes a doubling 
    /// modulo `2^Length(xs)-1`.
    operation CyclicRotateRegister (xs : LittleEndian) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);
            FanoutSwapReverseRegister(xs!);
            FanoutSwapReverseRegister(xs![1..(nQubits - 1)]);
        }
        adjoint auto;
        controlled auto;
        adjoint controlled auto;
    }

    //SHIFTS RIGHT
    operation CyclicRotateRegisterMultiple (xs : LittleEndian, nBits : Int) : Unit {
        body (...){
            let nQubits = Length(xs!);
            FanoutSwapReverseRegister(xs!);
            FanoutSwapReverseRegister(xs![0 .. nBits - 1]);
            FanoutSwapReverseRegister(xs![nBits .. nQubits - 1]);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Reverses the order of qubits in a register.
    /// When controlled, it uses
    /// a large number of ancillas but low depth.
    ///
    /// # Input
    /// ## xs
    /// The qubit array to be reversed.
    operation FanoutSwapReverseRegister(xs : Qubit[]) : Unit{
        body (...){
            SwapReverseRegister(xs);
        }
        controlled (controls, ...){
            if (IsMinimizeWidthCostMetric()) { //don't fanout with low width
                (Controlled SwapReverseRegister)(controls, (xs));
            } else {
                let nQubits = Length(xs);
                let nControls = nQubits / 2;
                if (nQubits == 2){
                    (Controlled SWAP)(controls, (xs[0], xs[1]));
                } elif (nQubits > 2){
                    using (singleControls = Qubit[nControls]){
                        (Controlled FanoutControls)(controls,(singleControls));
                        for (idxSwap in 0..nControls - 1){
                            (Controlled SWAP)([singleControls[idxSwap]], (xs[idxSwap], xs[nQubits - 1 - idxSwap]));
                        }
                        (Controlled Adjoint FanoutControls)(controls,(singleControls));
                    }
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Uses a tree of CNOT gates to "copy" an input qubit
    /// to an array of output qubits assumed to be 0.
    ///
    /// # Inputs
    /// ## input
    /// The qubit whose state (0 or 1) will be copied
    /// ## outputs
    /// An array of qubits initialized to 0 that will 
    /// be set to the same boolean value as `input`.
    ///
    /// # Reference
    /// Chrisopher Moore. "Quantum circuits : Fanout, 
    ///    Parity, and Counting."
    ///    https : //arxiv.org/pdf/quant-ph/9903046.pdf
    operation FanoutToZero(input : Qubit, outputs : Qubit[]) : Unit {
        body (...){
            let nQubits = Length(outputs);
            if (nQubits == 1){
                CNOT(input, outputs[0]);
            } elif (nQubits >= 2){
                let middle = nQubits / 2;
                CNOT(input, outputs[middle]);
                FanoutToZero(input, outputs[0..middle - 1]);
                FanoutToZero(outputs[middle], outputs[middle + 1..nQubits - 1]);
            }
        }
        controlled (controls, ...){
            let nQubits = Length(outputs);
            if (nQubits >= 1){
                (Controlled X)(controls + [input], (outputs[0]));
                FanoutToZero(outputs[0], outputs[1..nQubits - 1]);
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// When controlled, fans out the state of the control(s)
    /// to all of the input qubits with CNOTs.
    ///
    /// # Inputs
    /// ## singleControls
    /// Qubits assumed to be 0 which will be returned either all
    /// 1 (if the controls are all 1) or 0 (otherwise).
    operation FanoutControls(singleControls : Qubit[]) : Unit {
        body (...){
            // With no control, nothing to fanout
        }
        controlled (controls, ...){
            (Controlled X)(controls, singleControls[0]);
            FanoutToZero(singleControls[0], singleControls[1..Length(singleControls) - 1]);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Copies a qubit array to a larger qubit array.
    /// If the qubit array contains a word w and the output
    /// array contains 0s, this maps the output array to
    /// w || w || w || ...
    ///
    /// # Inputs
    /// ## register
    /// The register to be copied out
    /// ## outputRegister
    /// The register for the output
    ///
    /// # Remarks
    /// The length of the output register must be an exact multiple
    /// of the length of the input register
    operation FanoutRegister(register : Qubit[], outputRegister : Qubit[]) : Unit {
        body(...){
            let nQubits = Length(register);
            let nCopyQubits = Length(outputRegister);
            Fact (nCopyQubits % nQubits == 0, $"Cannot fanout {nQubits} qubits
                to {nCopyQubits} qubits because it is not an even multiple");
        
            for (idx in 0.. Length(register) - 1){
                FanoutToZero(register[idx], outputRegister[idx .. nQubits .. nCopyQubits - 1]);
            }
        }
        controlled (controls, ...){
            let nQubits = Length(register);
            let nCopyQubits = Length(outputRegister);
            Fact (nCopyQubits % nQubits == 0, $"Cannot fanout {nQubits} qubits
                to {nCopyQubits} qubits because it is not an even multiple");
            using (singleControls = Qubit[nQubits]){
                (Controlled FanoutControls)(controls, (singleControls));
                for (idx in 0.. Length(register) - 1){
                    (Controlled FanoutToZero)([singleControls[idx]], (register[idx], outputRegister[idx .. nQubits .. nCopyQubits - 1]));
                }
                (Controlled Adjoint FanoutControls)(controls, (singleControls));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Represents a qubit register that functions as a counter.
    ///
    /// # Contents
    /// ## register
    /// Points to the qubits used for the counter
    /// ## period
    /// The highest integer it can count to. Assumed
    /// to return to its zero state if it is incremented
    /// `period` times.
    /// ## Prepare
    /// Operation which initializes the qubit registers
    /// to the zero state of the counter.
    /// ## Increment
    /// Operation which increments the counter by one
    /// ## Test
    /// Operation which flips the target qubit if the
    /// counter is in any non-zero state.
    newtype Counter = (register : Qubit[], 
        period : Int, 
        Prepare : (Unit => Unit is Ctl + Adj), 
        Increment : (Unit => Unit is Ctl + Adj), 
        Test : ((Qubit) => Unit is Ctl + Adj)
    );

    /// # Summary
    /// Returns a qubit array as a Counter type.
    ///
    /// # Inputs
    /// ## register
    /// The qubits that wil form the counter.
    function QubitsAsCounter(register : Qubit[]) : Counter {
        return QubitsAsBasicCounter(register);
    }

    /// # Summary
    /// Formats a qubit array into a Counter type,
    /// including all necessary functions to act as a counter.
    ///
    /// # Inputs
    /// ## register
    /// The qubits that will act as the counter.
    ///
    /// # Output
    /// ## Counter
    /// A Counter that points to the qubits.
    function QubitsAsBasicCounter (register: Qubit[]) : Counter {
        let nQubits = Length(register);
        let incrementInternal = ConcatenateOperations(Increment, NoOp<Unit>, LittleEndian(register), _);
        let test = OppositeCheck(CheckIfAllZero(register, _), _);
        let prepare = NoOp<Unit>;
        return Counter(register, 2^nQubits, prepare, incrementInternal, test);
    }

    /// # Summary
    /// Performs the opposite test as a given test. 
    /// If the input test flips the target qubit if and only
    /// if some condition C holds, this will flip the target 
    /// if and only if C does not hold.
    ///
    /// # Inputs
    /// ## Test
    /// An operation which flips a qubit if some condition holds.
    /// Assumed to be curried on whatever inputs it checks.
    /// ## result
    /// Qubit to be flipped.
    operation OppositeCheck (test : (Qubit => Unit is Ctl + Adj), result : Qubit) : Unit {
        body (...){
            X(result);
            test(result);
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Checks if the input register is all zeros, and if so, 
    /// flips the output qubit from 0 to 1
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register being checked against all-zeros
    /// ## output
    /// The qubit that will be flipped
    operation CheckIfAllZero(xs : Qubit[], output : Qubit) : Unit {
        body (...){
            (Controlled CheckIfAllZero)(new Qubit[0], (xs, output));
        }
        controlled (controls, ...){
            ApplyToEachWrapperCA(X, xs);
            (Controlled CheckIfAllOnes)(controls, (xs, output));
            ApplyToEachWrapperCA(X, xs);
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Checks if the input register is all ones, and if so, 
    /// flips the output qubit from 0 to 1.
    /// # Inputs
    /// ## xs
    /// Qubit register being checked against all-zeros
    /// ## output
    /// The qubit that will be flipped
    ///
    /// # Remarks
    /// This has the same function as (Controlled X)(xs, (output))
    /// but this explicitly forms a binary tree to achieve a logarithmic
    /// depth. This means it borrows n-1 clean qubits.
    /// It also means that if xs has length 0, it flips the output
    operation CheckIfAllOnes(xs : Qubit[], output : Qubit) : Unit {
        body (...){
            let nQubits = Length(xs);
            if (nQubits == 0){
                X(output);
            } elif (nQubits == 1){
                CNOT(xs[0], output);
            } elif (nQubits == 2){
                CCNOTWrapper(xs[0], xs[1], output);
            } else {
                if (IsMinimizeWidthCostMetric()) {
                    LinearMultiControl(xs, output);
                } else { //high width but log-depth and small T-count
                    using ((spareControls, ancillaOutput) = (Qubit[nQubits - 2], Qubit())){
                        CompressControls(xs, spareControls, ancillaOutput);
                        CNOT(ancillaOutput, output);
                        (Adjoint CompressControls)(xs, spareControls, ancillaOutput);
                    }
                }
            }
        }
        controlled (controls, ...){
            CheckIfAllOnes(controls + xs, output);
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Flips the output qubit if and only if all the input qubits are 1.
    /// Uses a method with only 1 ancilla, but linear depth.
    ///
    /// # Inputs
    /// ## controlQubits
    /// Input qubits to check if 1
    /// ## output
    /// Output qubit to flip
    ///
    /// ## References
    /// A. Barenco, C.H. Bennett, R. Cleve, D.P. DiVincenzo, N. Margolus, 
    /// 	P. Shor, T. Sleator, J. Smolin, H. Weinfurter.
    /// 	"Elementary Gates for Quantum Computation"
    ///		https://arxiv.org/abs/quant-ph/9503016v1
    operation LinearMultiControl(controlQubits : Qubit[], output : Qubit) : Unit {
        body (...){
            let nQubits = Length(controlQubits);
            if (nQubits == 0){
                //do nothing
            } elif (nQubits == 1){
                CNOT(controlQubits[0], output);
            } elif (nQubits == 2){
                CCNOTWrapper(controlQubits[0], controlQubits[1], output);
            } elif (nQubits <= 4){
                borrowing (ancillaControl = Qubit()){
                    LinearMultiControl(controlQubits[0.. nQubits -2], ancillaControl);
                    CCNOTWrapper(controlQubits[nQubits - 1], ancillaControl, output);
                    LinearMultiControl(controlQubits[0.. nQubits -2], ancillaControl);
                    CCNOTWrapper(controlQubits[nQubits - 1], ancillaControl, output);
                }
            } elif (nQubits == 5) {
                borrowing (ancillaControl = Qubit()){
                    LinearMultiControl(controlQubits[0 .. nQubits - 3], ancillaControl);
                    LinearMultiControl(controlQubits[nQubits - 2 .. nQubits - 1] + [ancillaControl], output);
                    LinearMultiControl(controlQubits[0 .. nQubits - 3], ancillaControl);
                    LinearMultiControl(controlQubits[nQubits - 2 .. nQubits - 1] + [ancillaControl], output);
                }
            } else {
                borrowing (ancillaControl = Qubit()){
                    let m = (nQubits + 1) / 2;
                    CascadeControl(controlQubits[0 .. m - 1], ancillaControl);
                    CascadeControl(controlQubits[m .. nQubits - 1] + [ancillaControl], output);
                    CascadeControl(controlQubits[0 .. m - 1], ancillaControl);
                    CascadeControl(controlQubits[m .. nQubits - 1] + [ancillaControl], output);
                }
            }
        }
        controlled (controls, ...){
            LinearMultiControl(controls + controlQubits, output);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Flips an output qubit if and only if all inputs are 1.
    /// Uses a linear structure which uses 4n Toffoli gates.
    ///
    /// # Inputs
    /// ## controlQubits
    /// Qubits which must be all 1 to flip the output
    /// ## output
    /// Qubit to flip
    ///
    /// ## References
    /// A. Barenco, C.H. Bennett, R. Cleve, D.P. DiVincenzo, N. Margolus, 
    /// 	P. Shor, T. Sleator, J. Smolin, H. Weinfurter.
    /// 	"Elementary Gates for Quantum Computation"
    ///		https://arxiv.org/abs/quant-ph/9503016v1
    operation CascadeControl(controlQubits : Qubit[], output : Qubit) : Unit {
        body (...){
            let nQubits = Length(controlQubits);
            if (nQubits <= 2){
                LinearMultiControl(controlQubits, output);
            } else {
                borrowing (ancillaControls = Qubit[nQubits - 2]){
                    let ancillaTargets = [output] + ancillaControls;
                    for (idx in 0 .. nQubits - 3){
                        CCNOTWrapper(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                    }
                    CCNOTWrapper(controlQubits[nQubits - 2], controlQubits[nQubits -1], ancillaControls[nQubits - 3]);
                    for (idx in nQubits - 3 .. (-1) .. 0){
                        CCNOTWrapper(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                    }
                    for (idx in 1 .. nQubits - 3){
                        CCNOTWrapper(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                    }
                    CCNOTWrapper(controlQubits[nQubits - 2], controlQubits[nQubits -1], ancillaControls[nQubits - 3]);
                    for (idx in nQubits - 3 .. (-1) .. 1){
                        CCNOTWrapper(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                    }
                }
            }
        }
        controlled (controls, ...){
            CascadeControl(controls + controlQubits, output);
        }
        adjoint controlled auto;
    }




    /// # Summary
    /// Flips a blank output qubit if and only if all input
    /// control qubits are in the 1 state. Uses clean ancilla
    /// which are returned dirty.
    ///
    /// # Inputs
    /// ## controlQubits
    /// Array of qubits acting like a controlled X on the output
    /// ## blankControlQubits
    /// Qubits initialized to 0 which are used as ancilla.
    /// ## output 
    /// A qubit, assumed to be 0, which is flipped if all control
    /// qubits are 1
    ///
    /// # Remarks
    /// Identical in function to (Controlled X)(controlQubits, (output))
    /// except the depth is lower, the output must be 0, and it uses
    /// ancilla which are not uncomputed.
    /// If controlQubits has n qubits, then this needs n-2 
    /// blankControlQubits.
    operation CompressControls(controlQubits : Qubit[], blankControlQubits : Qubit[], output : Qubit) : Unit {
        body (...){
            let nControls = Length(controlQubits);
            let nNewControls = Length(blankControlQubits);
            if (nControls == 2){
                AndWrapper(controlQubits[0], controlQubits[1], output);
            } else {
                Fact(nNewControls >= nControls/2, $"Cannot compress {nControls}
                    control qubits to {nNewControls} qubits without more ancilla");
                Fact(nNewControls <= nControls, 
                    $"Cannot compress {nControls} control qubits into
                    {nNewControls} qubits because there are too few controls");
                let compressLength = nControls - nNewControls;
                for (idx in 0.. 2 .. nControls - 2){
                    AndWrapper(controlQubits[idx], controlQubits[idx + 1], blankControlQubits[idx/2]);
                }
                if (nControls % 2 == 0){
                    CompressControls(blankControlQubits[0.. nControls/2 - 1], blankControlQubits[nControls/2 .. nNewControls - 1], output);
                } else {
                    CompressControls([controlQubits[nControls - 1]] + blankControlQubits[0.. nControls/2 - 1], blankControlQubits[nControls/2 .. nNewControls - 1], output);
                }
            }
        }
        adjoint auto;
    }

    

    /// # Summary
    /// Runs a "quantum while loop". This runs a series of 
    /// unitaries U_1, ..., U_n. Before each unitary, a quantum Test operation
    /// is run. If Test comes out true (i.e., it flips a control), then the 
    /// loop will stop running any more U_k and will instead increment a special counter.
    /// Since the classical control does not know many iterations it will take, it runs up
    /// to some predetermined bound.
    ///
    /// # Inputs
    /// ## Body
    /// This specifies the unitary U_k, where k is the integer input. 
    /// ## Test
    /// This runs some test, and flips the qubit given as input if the test passes. 
    /// ## counter
    /// A SpecialCounter type that must be passed initially in the all-ones state. 
    /// ## bound
    /// The maximum number of iterations that the while loop could possible take.
    ///
    /// # Reference
    /// A generalization of the circuit for modular inversion from : 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remark
    /// This operation is well-defined for cases where the test never passes. 
    /// It assumes that calling Test will not change the result of calling
    /// Test again. 
    operation QuantumWhile(lowerBound : Int, upperBound : Int, Body : ((Int)=>Unit is Ctl + Adj), test : ((Qubit)=>Unit is Ctl + Adj), Alternate : ((Int)=>Unit is Ctl + Adj), counter : Counter) : Unit{
        body (...){
            (Controlled QuantumWhile)(new Qubit[0], (lowerBound, upperBound, Body, test, Alternate, counter));
        }	
        controlled (controls, ...){
            Fact(upperBound>lowerBound, $"Upper bound ({upperBound}) must be higher than lower bound ({lowerBound})");
            Fact(upperBound-lowerBound<counter::period, $"Counter's period is {counter::period} but may need to count {upperBound-lowerBound} iterations");
            using (mainControl = Qubit()){
	    	    // Use the main control if there are too many controls
	    	    if (Length(controls) > 1){
		    	    CheckIfAllOnes(controls, mainControl);
			        for (roundNum in 0..lowerBound - 1){
			            (Controlled Body)([mainControl], (roundNum));
			        }
			        (Adjoint CheckIfAllOnes)(controls, mainControl);
		        } else {
	    	        for (roundNum in 0..lowerBound - 1){
			   	        (Controlled Body)(controls, (roundNum));
			        }
	           }
	  	    for (roundNum in lowerBound..upperBound-1){
                    //Logic here : maincontrol is initially 0
                    //When the test does nothing and the counter is all 1s : 
                    //		It runs Body[idxRound], does not increment
                    //When the test is true but the counter is all 1s : 
                    //		It flips maincontrol from 0 to 1
                    //		The body is not run, the counter increments
                    //When the test is true and the counter is not all 1s : 
                    //		It flips maincontrol twice, keeping it at 1
                    //		The body is not run, the counter increments

                    //Runs the test
                    (Controlled test)(controls, (mainControl));
                    //Checks if the counter is non-start
                    counter::Test(mainControl);
                    //Fanout the main control to save depth
                    using (extraControls = Qubit[2]){
                        CNOT(mainControl,extraControls[0]);
                        CNOT(extraControls[0],extraControls[1]);
                        //Runs the body if maincontrol is 0
                        (Controlled X)(controls, (mainControl));
                        (Controlled Body)([mainControl], (roundNum));
                        (Controlled X)(controls, (mainControl));
                        //Increments the counter if need be
                        (Controlled counter::Increment)([extraControls[0]], ());
                        //Otherwise, runs the alternate
                        (Controlled Alternate)([extraControls[1]], (roundNum));
                        CNOT(extraControls[0],extraControls[1]);
                        CNOT(mainControl,extraControls[0]);
                    }
                }
                //Clears the control
                //If the test was positive at any point, maincontrol
                //should be 1.
                //Otherwise, it will be 0. 
                //To test whether the test was ever positive, we check the
                // counter
                (Controlled counter::Test)(controls, (mainControl));
            }
        }
        controlled adjoint auto;
    }


    
}