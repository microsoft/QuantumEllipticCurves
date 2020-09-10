// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Tests{
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Logical;
	open Microsoft.Quantum.Measurement;
	open Microsoft.Quantum.Arithmetic;
	open Microsoft.Quantum.Diagnostics;
	open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Math;
	open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Basics;


    operation CCNOTTestHelper(
        CCNOTOp : ((Qubit, Qubit, Qubit) => Unit is Adj),
        control1 : Bool,
        control2 : Bool,
        inputTarget : Bool
    ) : Unit {
        using ((qControl1, qControl2, qTarget) = (Qubit(), Qubit(), Qubit())){
            let expected = Xor(control1 and control2, inputTarget);

            mutable mControl1 = false;
            mutable mControl2 = false;
            mutable mTarget = false;

            if (control1){X(qControl1);}
            if (control2){X(qControl2);}
            if (inputTarget){X(qTarget);}

            CCNOTOp(qControl1, qControl2, qTarget);

            set mControl1 = ResultAsBool(M(qControl1));
            set mControl2 = ResultAsBool(M(qControl2));
            set mTarget = ResultAsBool(M(qTarget));
            Reset(qControl2);
            Reset(qControl1);
            Reset(qTarget);
            Fact(mControl1 == control1, $"Control 1, input {control1},{control2},{inputTarget}: Expected {control1}, got {mControl1}");
            Fact(mControl2 == control2, $"Control 2, input {control1},{control2},{inputTarget}: Expected {control2}, got {mControl2}");
            Fact(mTarget == expected, $"Target, input {control1},{control2},{inputTarget}: Expected {expected}, got {mTarget}");
        }

    }

    operation CCNOTExhaustiveTestHelper(CCNOTOp : ((Qubit, Qubit, Qubit) => Unit is Adj)) : Unit {
        mutable control1 = false;
        mutable control2 = false;
        mutable target = false;
        for (idx1 in 0..1){
           for (idx2 in 0..1){
                for (idx3 in 0..1){

                    set target = not target;
                }
                set control2 = not control2;
            }
            set control1 = not control1;
        }
    }

    operation CCNOTTest() : Unit {
        CCNOTExhaustiveTestHelper(ccnot_T_depth_3);
    }



    operation CheckIfAllOnesTestHelper(
        OnesTest : ((Qubit[], Qubit) => Unit is Ctl + Adj),
        testValue : BigInt,
        nQubits : Int
    ) : Unit {
        using ((valueQubits, output) = (Qubit[nQubits], Qubit())){
            let expected = (2L^nQubits - 1L == testValue) ? One | Zero;
            let qValue = LittleEndian(valueQubits);
            mutable actualValue = 0L;
            mutable actualOutput = Zero;

             //Write to qubit registers
            ApplyXorInPlaceL(testValue, qValue);

            //Run Test
            OnesTest(valueQubits, output);

            set actualValue = MeasureBigInteger(qValue);
            Fact(actualValue == testValue, $"Input: Expected {testValue}, got {actualValue}");
            set actualOutput = M(output);
            Reset(output);
            Fact(actualOutput == expected, $"On input {testValue}, expected {expected}, got {actualOutput}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                     //Write to qubit registers
                     ApplyXorInPlaceL(testValue, qValue);

                     //Run Test
                    (Controlled OnesTest)(controls, (valueQubits, output));

                    //check results
                    set actualValue = MeasureBigInteger(qValue);
                    Fact(actualValue == testValue, $"Control 0: Input: Expected {testValue}, got {actualValue}");
                    set actualOutput = M(output);
                    Reset(output);
                    Fact(actualOutput == Zero, $"Control 0: On input {testValue}, expected zero, got {actualOutput}");
   
                    // now controls are set to |1>
                    ApplyToEach(X, controls);

                      //Write to qubit registers
                     ApplyXorInPlaceL(testValue, qValue);

                     //Run Test
                    (Controlled OnesTest)(controls, (valueQubits, output));

                    //check results
                    set actualValue = MeasureBigInteger(qValue);
                    Fact(actualValue == testValue, $"Control 1: Input: Expected {testValue}, got {actualValue}");
                    set actualOutput = M(output);
                    Reset(output);
                    Fact(actualOutput == expected, $"Control 1: On input {testValue}, expected {expected}, got {actualOutput}");
                    ResetAll(controls);
                }
            }
        }
    }


    operation CheckIfAllOnesReversibleTestHelper(
        OnesTest : ((Qubit[], Qubit) => Unit is Ctl + Adj),
        nQubits : Int) : Unit{
        for (problemSize in 1 .. nQubits){
            for (value in 0 .. 2^(problemSize - 1) - 1){
                CheckIfAllOnesTestHelper(OnesTest, IntAsBigInt(value), nQubits);
            }
        }
    }

    operation CheckIfAllOnesReversibleTest() : Unit {
        let nQubits = 10;
        CheckIfAllOnesReversibleTestHelper(CheckIfAllOnes, nQubits);
    }

operation EqualLookupTestHelper( 
    LookUp : ((BigInt[], ((BigInt) => Unit is Ctl + Adj), LittleEndian) => Unit is Ctl),
    table : BigInt[],
    address : Int,
    addressSize : Int
) : Unit {
    body (...) {
        using ((addressQubits, outputQubits) = (Qubit[addressSize], Qubit[addressSize])){
            // Bookkeeping and qubit allocation
            let qAddress = LittleEndian(addressQubits);
            let qValue = LittleEndian(outputQubits);
            mutable outputValue = 0L;
            mutable readAddress = 0L;

            //Write to qubit registers
            ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

            //Run Test
            LookUp(table, ApplyXorInPlaceL(_, qValue) , qAddress);

            // Check results
            set outputValue = MeasureBigInteger(qValue);
            Fact(outputValue == table[address], $"Value: Expected {table[address]} at address {address}, got {outputValue}");
            set readAddress = MeasureBigInteger(qAddress);
            Fact(readAddress == IntAsBigInt(address), $"Address: Expected {address}, got {readAddress}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
                    //write to qubit registers
                    ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

                    //run test
                    (Controlled LookUp)(controls, (table, ApplyXorInPlaceL(_, qValue), qAddress));

                    //check results
                    set outputValue = MeasureBigInteger(qValue);
                    Fact(outputValue == 0L, $"Control 0: Value: Expected {0L} at address {address}, got {outputValue}");
                    set readAddress = MeasureBigInteger(qAddress);
                    Fact(readAddress == IntAsBigInt(address), $"Control 0: Address: Expected {address}, got {readAddress}");
   
                    // now controls are set to |1>
                    ApplyToEach(X, controls);

                     //write to qubit registers
                    ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

                     //run test
                    (Controlled LookUp)(controls, (table, ApplyXorInPlaceL(_, qValue), qAddress));

                    //check results
                    set outputValue = MeasureBigInteger(qValue);
                    Fact(outputValue == table[address], $"Control 1: Value: Expected {table[address]} at address {address}, got {outputValue}");
                    set readAddress = MeasureBigInteger(qAddress);
                    Fact(readAddress == IntAsBigInt(address), $"Control 1: Address: Expected {address}, got {readAddress}");
                    ResetAll(controls);

                }
            }
        }
    }
}

operation EqualLookUpExhaustiveTestHelper(
    LookUp : ((BigInt[], ((BigInt) => Unit is Ctl + Adj), LittleEndian) => Unit is Ctl),
    addressSize : Int
) : Unit {
    mutable bigTable = [0L];
    for (i in 1 .. 2 ^ addressSize - 1){
        set bigTable = bigTable + [IntAsBigInt(i)];
    }
    let address = Microsoft.Quantum.Random.DrawRandomInt(0, 2 ^ addressSize - 1);
    EqualLookupTestHelper(LookUp, bigTable, address, addressSize);
}

operation EqualLookupExhaustiveReversibleTest() : Unit {
    let addressSize = 6;
    EqualLookUpExhaustiveTestHelper(EqualLookup<BigInt>, addressSize);
}



	
////////////// INTEGER ADDITION WITH CARRY //////////////////
///
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
///
/// # Operations
/// This will test:
///		* RippleCarryAdderD
///		* RippleCarryAdderCDKM
///		* RippleCarryAdderTTK
///		* CarryLookAheadAdder

 operation IntegerAdderTestHelper( IntegerAdderToTest : ( (LittleEndian, LittleEndian, Qubit) => Unit is Ctl + Adj), summand1 : BigInt, summand2 : BigInt, numberOfQubits : Int ) : Unit {
        body (...) {
            using (register = Qubit[2*numberOfQubits + 1]) {
				// Bookkeeping and qubit allocation
                mutable actual_carry = 0L;
                mutable actual1 = 0L;
                mutable actual2 = 0L;
                mutable measured_carry = Zero;
                let summand1LE = LittleEndian(register[0 .. numberOfQubits - 1]);
                let summand2LE = LittleEndian(register[numberOfQubits .. 2*numberOfQubits - 1]);
                let carry = register[2*numberOfQubits];

				// Write to qubit registers
                ApplyXorInPlaceL(summand1, summand1LE);
                ApplyXorInPlaceL(summand2, summand2LE);

				// Run test
                IntegerAdderToTest(summand1LE, summand2LE, carry);
 
				// Compute expected classical result
                let sum = summand1 + summand2;
                let expected_sum = (sum)%IntAsBigInt(2^numberOfQubits);
                let difference_carry = (summand1 > summand2);
                let difference = summand2 - summand1;
                let expected_difference = difference_carry ? difference + IntAsBigInt(2^numberOfQubits) | difference;

				//Check sum results
                set actual1 = MeasureBigInteger(summand1LE);
                Fact(summand1==actual1, $"Summand 1: Expected {summand1}, got {actual1}");
                set actual2 = MeasureBigInteger(summand2LE);
                Fact(expected_sum==actual2, $"Sum: Expected {expected_sum}, got {actual2}");
                let expected_carry = (sum / IntAsBigInt(2^numberOfQubits));
                set measured_carry = MResetZ(carry);
                if (measured_carry == One) {set actual_carry = 1L;} else {set actual_carry = 0L;}
                Fact(expected_carry==actual_carry, $"Carry: Expected {expected_carry}, got {actual_carry}");

                //Difference

                // Write to qubit registers
                ApplyXorInPlaceL(summand1, summand1LE);
                ApplyXorInPlaceL(summand2, summand2LE);

                //Check difference results
                // Run test
                (Adjoint IntegerAdderToTest)(summand1LE, summand2LE, carry);

                //Check difference results
                set actual1 = MeasureBigInteger(summand1LE);
                Fact(summand1==actual1, $"Summand 1: Expected {summand1}, got {actual1}");
                set actual2 = MeasureBigInteger(summand2LE);
                Fact(expected_difference==actual2, $"Difference: Expected {expected_difference}, got {actual2}");
                
                set measured_carry = MResetZ(carry);
                Fact(difference_carry == ResultAsBool(measured_carry), $"Difference Carry: Expected {difference_carry}, got {measured_carry}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
						// Write to qubit registers
                        ApplyXorInPlaceL(summand1, summand1LE);
                        ApplyXorInPlaceL(summand2, summand2LE);

                        // controls are |0>, no addition is computed
						//Run test
                        (Controlled IntegerAdderToTest) (controls, (summand1LE, summand2LE, carry));

						//Check results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1== actual1, $"Control 0, summand 1: Expected {summand1}, got {actual1}");
                        set actual2 = MeasureBigInteger(summand2LE);
                        Fact(summand2== actual2, $"Control 0, sum: Expected {expected_sum}, got {actual2}");
                        set measured_carry = MResetZ(carry);
                        if (measured_carry == One) {set actual_carry = 1L;} else {set actual_carry = 0L;}
                        Fact(0L== actual_carry, $"Control 0, carry: Expected {0}, got {actual_carry}");

                        //Control 0 Difference

                        // Write to qubit registers
                        ApplyXorInPlaceL(summand1, summand1LE);
                        ApplyXorInPlaceL(summand2, summand2LE);

                        //Check difference results
                        // Run test
                        (Controlled Adjoint IntegerAdderToTest)(controls, (summand1LE, summand2LE, carry));

                        //Check difference results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1==actual1, $"Control 0, Summand 1: Expected {summand1}, got {actual1}");
                        set actual2 = MeasureBigInteger(summand2LE);
                        Fact(summand2==actual2, $"Control 0, Difference: Expected {expected_difference}, got {actual2}");
                        set measured_carry = MResetZ(carry);
                        Fact(Zero == measured_carry, $"Control 0, Difference Carry: Expected {false}, got {measured_carry}");



                        //Control 1

						//Write to qubit registers
                        ApplyXorInPlaceL(summand1, summand1LE);
                        ApplyXorInPlaceL(summand2, summand2LE);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

						// Run test
                        (Controlled IntegerAdderToTest) (controls, (summand1LE, summand2LE, carry));

						//Check results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1== actual1, $"Control 1, summand 1: Expected {summand1}, got {actual1}");
                        set actual2 = MeasureBigInteger(summand2LE);
                        Fact(expected_sum == actual2, $"Control 1, sum: Expected {expected_sum}, got {actual2}");
                        set measured_carry = MResetZ(carry);
                        if (measured_carry == One) {set actual_carry = 1L;} else {set actual_carry = 0L;}
                        Fact(expected_carry== actual_carry, $"Control 1, carry: Expected {expected_carry}, got {actual_carry}");

                        //Difference

                        // Write to qubit registers
                        ApplyXorInPlaceL(summand1, summand1LE);
                        ApplyXorInPlaceL(summand2, summand2LE);

                        //Check difference results
                        // Run test
                        (Controlled Adjoint IntegerAdderToTest)(controls, (summand1LE, summand2LE, carry));

                        //Check difference results
                        set actual1 = MeasureBigInteger(summand1LE);
                        Fact(summand1==actual1, $"Control 1, Summand 1: Expected {summand1}, got {actual1}");
                        set actual2 = MeasureBigInteger(summand2LE);
                        Fact(expected_difference==actual2, $"Control 1, Difference: Expected {expected_difference}, got {actual2}");
                        set measured_carry = MResetZ(carry);
                        Fact(difference_carry == ResultAsBool(measured_carry), $"Control 1, Difference Carry: Expected {difference_carry}, got {measured_carry}");



                        ResetAll(controls);
                    }
                }
            }
        }
    }
 
    operation IntegerAdderExhaustiveTestHelper (IntegerAdderToTest : ( (LittleEndian, LittleEndian, Qubit) => Unit is Ctl + Adj), numberOfQubits : Int) : Unit {
        for( summand1 in 0 .. 2^numberOfQubits - 1 ) {
            for( summand2 in 0 .. 2^numberOfQubits - 1 ) {
                IntegerAdderTestHelper(IntegerAdderToTest, IntAsBigInt(summand1), IntAsBigInt(summand2), numberOfQubits);
            }
        }
    }

	operation CarryLookAheadAdderExhaustiveTest (): Unit {
		let numberOfQubits = 4;
		IntegerAdderExhaustiveTestHelper(CarryLookAheadAdder,numberOfQubits);
	}
	operation CarryLookAheadAdderExhaustiveReversibleTest (): Unit {
		let maxNumberOfQubits = 8;
		let minNumberOfQubits = 1;
		for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
			IntegerAdderExhaustiveTestHelper(CarryLookAheadAdder,numberOfQubits);
		}
	}

    operation CDKMGAdderExhaustiveTest (): Unit {
        let numberOfQubits = 4;
        IntegerAdderExhaustiveTestHelper(CDKMGAdder,numberOfQubits);
    }
    operation CDKMGAdderExhaustiveReversibleTest (): Unit {
        let maxNumberOfQubits = 8;
        let minNumberOfQubits = 1;
        for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
            IntegerAdderExhaustiveTestHelper(CDKMGAdder,numberOfQubits);
        }
    }

    operation AdderExhaustiveTest () : Unit{
         let numberOfQubits = 4;
         IntegerAdderExhaustiveTestHelper(AddInteger, numberOfQubits);
    }
      operation AdderExhaustiveReversibleTest (): Unit {
        let maxNumberOfQubits = 8;
        let minNumberOfQubits = 1;
        for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
            IntegerAdderExhaustiveTestHelper(AddInteger,numberOfQubits);
        }
    }

	///////////////// INTEGER ADDITION WITHOUT CARRY /////////////////
	///
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
	///
	/// # Operations
	/// This will test: 
	///		* RippleCarryAdderNoCarryTTK
	///		* CarryLookAheadAdderNoCarry
    operation IntegerAdderNoCarryTestHelper( IntegerAdderToTest : ( (LittleEndian, LittleEndian) => Unit is Ctl), summand1 : BigInt, summand2 : BigInt, numberOfQubits : Int ) : Unit {
        using (register = Qubit[2*numberOfQubits]) {
			// Bookkeeping and qubit allocation
            mutable actual1 = 0L;
            mutable actual2 = 0L;
            let summand1LE = LittleEndian(register[0 .. numberOfQubits - 1]);
            let summand2LE = LittleEndian(register[numberOfQubits .. 2*numberOfQubits - 1]);
 
			// Write to qubit registers
            ApplyXorInPlaceL(summand1, summand1LE);
            ApplyXorInPlaceL(summand2, summand2LE);

			// Run test
            IntegerAdderToTest(summand1LE, summand2LE);
 
			// Compute expected classical result
            let sum = summand1 + summand2;
            let expected = sum % IntAsBigInt(2^numberOfQubits);

			//Check results
            set actual1 = MeasureBigInteger(summand1LE);
            Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
            set actual2 = MeasureBigInteger(summand2LE);
            Fact(expected== actual2, $"Expected {expected}, got {actual2}");
            let expected_carry = (sum / IntAsBigInt(2^numberOfQubits));

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
					//Write to qubit regiters
                    ApplyXorInPlaceL(summand1, summand1LE);
                    ApplyXorInPlaceL(summand2, summand2LE);

                    // controls are |0>, no addition is computed
					// Run test
                    (Controlled IntegerAdderToTest) (controls, (summand1LE, summand2LE));

					// Check results
                    set actual1 = MeasureBigInteger(summand1LE);
                    Fact(summand1== actual1, $"Expected {summand1}, got {actual1}");
                    set actual2 = MeasureBigInteger(summand2LE);
                    Fact(summand2== actual2, $"Expected {expected}, got {actual2}");

					// Write to qubit registers
                    ApplyXorInPlaceL(summand1, summand1LE);
                    ApplyXorInPlaceL(summand2, summand2LE);

                    // now controls are set to |1>, addition is computed
                    ApplyToEach(X, controls);

					//Run test
                    (Controlled IntegerAdderToTest) (controls, (summand1LE, summand2LE));

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

    operation IntegerAdderNoCarryExhaustiveTestHelper (IntegerAdderToTest : ( (LittleEndian, LittleEndian) => Unit is Ctl), numberOfQubits : Int) : Unit {
        for( summand1 in 0 .. 2^numberOfQubits - 1 ) {
            for( summand2 in 0 .. 2^numberOfQubits - 1 ) {
                IntegerAdderNoCarryTestHelper(IntegerAdderToTest, IntAsBigInt(summand1), IntAsBigInt(summand2), numberOfQubits);
            }
        }
    }

    operation RippleCarryAdderNoCarryTTKReversibleTest () : Unit {
        let numberOfQubits = 10;
        let summand1 = 1021L; 
        let summand2 = 973L; 
        IntegerAdderNoCarryTestHelper(RippleCarryAdderNoCarryTTK, summand1, summand2, numberOfQubits);
    }

    operation RippleCarryAdderNoCarryTTKExhaustiveTest () : Unit {
        let numberOfQubits = 4;
        IntegerAdderNoCarryExhaustiveTestHelper (RippleCarryAdderNoCarryTTK, numberOfQubits);
    }

    operation RippleCarryAdderNoCarryTTKExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..6) {
            IntegerAdderNoCarryExhaustiveTestHelper (RippleCarryAdderNoCarryTTK, numberOfQubits);
        }
    }
	operation CarryLookAheadAdderNoCarryExhaustiveTest (): Unit {
		let numberOfQubits = 4;
		IntegerAdderNoCarryExhaustiveTestHelper(CarryLookAheadAdderNoCarry,numberOfQubits);
	}
	operation CarryLookAheadAdderNoCarryExhaustiveReversibleTest (): Unit {
		let maxNumberOfQubits = 8;
		let minNumberOfQubits = 1;
		for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
			IntegerAdderNoCarryExhaustiveTestHelper(CarryLookAheadAdderNoCarry,numberOfQubits);
		}
	}

    operation CDKMGAdderNoCarryExhaustiveTest (): Unit {
        let numberOfQubits = 4;
        IntegerAdderNoCarryExhaustiveTestHelper(CDKMGAdderNoCarry,numberOfQubits);
    }
    operation CDKMGAdderNoCarryExhaustiveReversibleTest (): Unit {
        let maxNumberOfQubits = 8;
        let minNumberOfQubits = 1;
        for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
            IntegerAdderNoCarryExhaustiveTestHelper(CDKMGAdderNoCarry,numberOfQubits);
        }
    }

    operation AdderNoCarryExhaustiveTest (): Unit {
        let numberOfQubits = 4;
        IntegerAdderNoCarryExhaustiveTestHelper(AddIntegerNoCarry ,numberOfQubits);
    }
    operation AdderNoCarryExhaustiveReversibleTest (): Unit {
        let maxNumberOfQubits = 8;
        let minNumberOfQubits = 1;
        for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
            IntegerAdderNoCarryExhaustiveTestHelper(AddIntegerNoCarry ,numberOfQubits);
        }
    }

	///////////////// CONSTANT ADDITION /////////////////
	///
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
	/// # Operations
	/// This can test:
	///		* CarryLookAheadAddConstant
	///		* _AddConstantLowWidth
	///		* _AddConstantLowT
	operation AddConstantTestHelper(Adder:((BigInt,LittleEndian)=>Unit is Ctl), constant : BigInt, integer : BigInt, numberOfQubits : Int ) : Unit {
        body (...) {
            using (register = Qubit[numberOfQubits + 2]) {
				// Bookkeeping and qubit allocation
                mutable actual = 0L;
                let integerLE = LittleEndian(register[0 .. numberOfQubits - 1]);
 
				// Write to qubit register
                ApplyXorInPlaceL(integer, integerLE);

				//Run Test
                Adder(constant, integerLE);
 
				//Compute expected classical result
                let expected = (integer + constant) % IntAsBigInt(2^numberOfQubits);

				// Check results
                set actual = MeasureBigInteger(integerLE);
                Fact(expected== actual, $"Expected {expected}, got {actual}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
						// Write to qubit register
                        ApplyXorInPlaceL(integer, integerLE);

                        // controls are |0>, no addition is computed
						// Run test
                        (Controlled Adder) (controls, (constant, integerLE));

						// Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(integer== actual, $"Expected {integer}, got {actual}");

						//Write to qubit regsiter
                        ApplyXorInPlaceL(integer, integerLE);

						// controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);
                        
						// Run test
                        (Controlled Adder) (controls, (constant, integerLE));

						//Check results
                        set actual = MeasureBigInteger(integerLE);
                        Fact(expected==actual, $"Expected {expected}, got {actual}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation AddConstantExhaustiveTestHelper (Adder:((BigInt,LittleEndian)=>Unit is Ctl),numberOfQubits : Int) : Unit {
        body (...) {
            for( constant in 0 .. 2^numberOfQubits - 1 ) {
                for( integer in 0 .. 2^numberOfQubits - 1 ) {
                    AddConstantTestHelper(Adder,IntAsBigInt(constant), IntAsBigInt(integer), numberOfQubits);
                }
            }
        }
    }

    operation AddConstantTest () : Unit {
        body (...) {
            let numberOfQubits = 7;
            let constant = 18L;
            let integer = 111L; 
            AddConstantTestHelper(AddConstant,constant, integer, numberOfQubits);
        }
    }

    operation AddConstantExhaustiveTest () : Unit {
        body (...) {
            let numberOfQubits = 3;
            AddConstantExhaustiveTestHelper (AddConstant,numberOfQubits);
        }
    }

    operation AddConstantReversibleTest () : Unit {
        body (...) {
            let numberOfQubits = 17;
            let integer = 31579L;
            let constant = 11111L; 
            AddConstantTestHelper(AddConstant,constant, integer, numberOfQubits);
        }
    }

    operation AddConstantExhaustiveReversibleTest () : Unit {
        body (...) {
            let numberOfQubits = 5;
            AddConstantExhaustiveTestHelper (AddConstant,numberOfQubits);
        }
    }

  operation AddConstantNoCarryExhaustiveTest () : Unit {
        body (...) {
            let numberOfQubits = 4;
            AddConstantExhaustiveTestHelper (CarryLookAheadAddConstant,numberOfQubits);
        }
    }

    operation AddConstantNoCarryReversibleTest () : Unit {
        body (...) {
            let numberOfQubits = 17;
            let integer = 31579L;
            let constant = 11111L; 
            AddConstantTestHelper(CarryLookAheadAddConstant,constant, integer, numberOfQubits);
        }
    }

    operation AddConstantNoCarryExhaustiveReversibleTest () : Unit {
        body (...) {
			let maxNumberOfQubits = 8;
			let minNumberOfQubits = 1;
			for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
				AddConstantExhaustiveTestHelper (CarryLookAheadAddConstant,numberOfQubits);
			}
        }
    }

    operation AddConstantCDKMGNoCarryReversibleTest () : Unit {
        body (...) {
            let numberOfQubits = 17;
            let integer = 31579L;
            let constant = 11111L; 
            AddConstantTestHelper(CDKMGAddConstant,constant, integer, numberOfQubits);
        }
    }

    operation AddConstantCDKMGNoCarryExhaustiveReversibleTest () : Unit {
        body (...) {
            let maxNumberOfQubits = 8;
            let minNumberOfQubits = 1;
            for (numberOfQubits in minNumberOfQubits .. maxNumberOfQubits){
                AddConstantExhaustiveTestHelper (CDKMGAddConstant,numberOfQubits);
            }
        }
    }

	///////////////// GREATER THAN /////////////////
	///
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
	/// # Operations
	/// This can test:
	///		* GreaterThanLookAhead
	///		* GreaterThan
    operation GreaterThanTestHelper(Comparator:((LittleEndian,LittleEndian,Qubit)=>Unit is Ctl), integer1 : BigInt, integer2 : BigInt, numberOfQubits : Int ) : Unit {
        using (register = Qubit[2*numberOfQubits+1]) {
			// Bookkeeping and qubit allocation
            mutable actual1 = 0L;
            mutable actual2 = 0L;
            mutable actualr = Zero;
            mutable gt = Zero;
            let integer1LE = LittleEndian(register[0 .. numberOfQubits - 1]);
            let integer2LE = LittleEndian(register[numberOfQubits .. 2*numberOfQubits - 1]);
            let result = register[2*numberOfQubits];
 
			// Write to qubit registers
            ApplyXorInPlaceL(integer1, integer1LE);
            ApplyXorInPlaceL(integer2, integer2LE);

			// Run test
            Comparator(integer1LE, integer2LE, result);

			// Compute expected classical result
            if (integer1 > integer2) {set gt = One;} 

			// Check results
            set actual1 = MeasureBigInteger(integer1LE);
            Fact(integer1== actual1, $"Expected {integer1}, got {actual1}");
            set actual2 = MeasureBigInteger(integer2LE);
            Fact(integer2== actual2, $"Expected {integer2}, got {actual2}");
            set actualr = M(result);
			Reset(result);
            EqualityFactB((gt == actualr), true, $"Expected {gt}, got {actualr}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
					// Write to qubit register
                    ApplyXorInPlaceL(integer1, integer1LE);
                    ApplyXorInPlaceL(integer2, integer2LE);

					//Run test
                    (Controlled Comparator) (controls, (integer1LE, integer2LE, result));

					// Check results
                    set actual1 = MeasureBigInteger(integer1LE);
                    Fact(integer1== actual1, $"Expected {integer1}, got {actual1}");
                    set actual2 = MeasureBigInteger(integer2LE);
                    Fact(integer2== actual2, $"Expected {integer2}, got {actual2}");
                    set actualr = M(result);
                    EqualityFactB((actualr == Zero), true, $"Expected Zero, got {actualr}");

					// Flip controls
                    ApplyToEach(X, controls);

					// Write to qubit registers
                    ApplyXorInPlaceL(integer1, integer1LE);
                    ApplyXorInPlaceL(integer2, integer2LE);

					// Run test
                    (Controlled Comparator) (controls, (integer1LE, integer2LE, result));

					// Check results
                    set actual1 = MeasureBigInteger(integer1LE);
                    Fact(integer1== actual1, $"Expected {integer1}, got {actual1}");
                    set actual2 = MeasureBigInteger(integer2LE);
                    Fact(integer2== actual2, $"Expected {integer2}, got {actual2}");
                    set actualr = M(result);
					Reset(result);
                    EqualityFactB((gt == actualr), true, $"Expected {gt}, got {actualr}");

                    ResetAll(controls);
                }
            }
        }
    }

    operation GreaterThanExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..5) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanTestHelper(GreaterThanWrapper ,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

	operation GreaterThanLookAheadExhaustiveTest () : Unit {
        for (numberOfQubits in 1..5) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanTestHelper(GreaterThanLookAhead,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

    operation GreaterThanLookAheadExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..7) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanTestHelper(GreaterThanLookAhead,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

    operation GreaterThanCDKMGExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..7) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanTestHelper(CKDMGGreaterThan, IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

	///////////////// GREATER THAN CONSTANT /////////////////
	///
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
	///
	/// # Operations
	/// This can test:
	///		* GreaterThanConstantLookAhead
	operation GreaterThanConstantTestHelper(Comparator:((BigInt,LittleEndian,Qubit)=>Unit is Ctl), constant : BigInt, integer : BigInt, numberOfQubits : Int ) : Unit {
        using (register = Qubit[numberOfQubits+1]) {
            mutable actual = 0L;
            mutable actualr = Zero;
            mutable gt = Zero;
            let integerLE = LittleEndian(register[0 .. numberOfQubits - 1]);
            let result = register[numberOfQubits];
 
            ApplyXorInPlaceL(integer, integerLE);

            Comparator(constant, integerLE, result);

            if (integer > constant) {set gt = One;} 
            set actual = MeasureBigInteger(integerLE);
            Fact(integer== actual, $"Expected {integer}, got {actual}");
            set actualr = M(result);
            EqualityFactB((gt == actualr), true, $"Expected {gt}, got {actualr}");

            Reset(result);
            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
				    ApplyXorInPlaceL(integer, integerLE);
                    (Controlled Comparator) (controls, (constant,integerLE, result));

                    set actual = MeasureBigInteger(integerLE);
                    Fact(integer== actual, $"Control 0: Expected {integer}, got {actual}");
                    set actualr = M(result);
                    EqualityFactB((actualr == Zero), true, $"Control 0: Expected Zero, got {actualr}");

                    ApplyToEach(X, controls);
                    ApplyXorInPlaceL(integer, integerLE);
                    (Controlled Comparator) (controls, (constant,integerLE, result));

                    set actual = MeasureBigInteger(integerLE);
                    Fact(integer== actual, $"Control 1: Expected {integer}, got {actual}");
                    set actualr = M(result);
                    EqualityFactB((gt == actualr), true, $"Control 1: Expected {gt}, got {actualr}");

                    ResetAll(controls);
                    Reset(result);
                }
            }
        }
    }
	operation GreaterThanConstantLookAheadExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..7) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanConstantTestHelper(GreaterThanConstantLookAhead,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

	operation GreaterThanConstantLookAheadExhaustiveTest () : Unit {
        for (numberOfQubits in 1..5) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanConstantTestHelper(GreaterThanConstantLookAhead,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

    operation GreaterThanConstantExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..7) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanConstantTestHelper(GreaterThanConstant,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

    operation GreaterThanConstantExhaustiveTest () : Unit {
        for (numberOfQubits in 1..5) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    GreaterThanConstantTestHelper(GreaterThanConstant,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

	///////////////// LESS THAN CONSTANT /////////////////
	///
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
	/// 
	/// # Operations
	/// This can test:
	///		* LessThanConstantLookAhead
	operation LessThanConstantTestHelper(Comparator:((BigInt,LittleEndian,Qubit)=>Unit is Ctl), constant : BigInt, integer : BigInt, numberOfQubits : Int ) : Unit {
        using (register = Qubit[numberOfQubits+1]) {
			// Bookkeeping and qubit allocation
            mutable actual = 0L;
            mutable actualr = Zero;
            mutable gt = Zero;
            let integerLE = LittleEndian(register[0 .. numberOfQubits - 1]);
            let result = register[numberOfQubits];
 
			// Write to qubit register
            ApplyXorInPlaceL(integer, integerLE);

			// Run test
            Comparator(constant, integerLE, result);

			// Compute expected classical result
            if (integer < constant) {set gt = One;} 

			// Run test
            set actual = MeasureBigInteger(integerLE);
            Fact(integer== actual, $"Expected {integer}, got {actual}");
            set actualr = M(result);
			Reset(result);
            EqualityFactB((gt == actualr), true, $"Expected {gt}, got {actualr}");

            for (numberOfControls in 1..2) { 
                using (controls = Qubit[numberOfControls]) {
					//Write to qubit registers
				    ApplyXorInPlaceL(integer, integerLE);

					// Run test
                    (Controlled Comparator) (controls, (constant,integerLE, result));

					// Check results
                    set actual = MeasureBigInteger(integerLE);
                    Fact(integer== actual, $"Control 0: Expected {integer}, got {actual}");
                    set actualr = M(result);
                    EqualityFactB((actualr == Zero), true, $"Control 0: Expected Zero, got {actualr}");

					// Flip controls
                    ApplyToEach(X, controls);

					// Write to qubit register
                    ApplyXorInPlaceL(integer, integerLE);

					//Run test
                    (Controlled Comparator) (controls, (constant,integerLE, result));

					//Check results
                    set actual = MeasureBigInteger(integerLE);
                    Fact(integer== actual, $"Control 1: Expected {integer}, got {actual}");
                    set actualr = M(result);
                    Reset(result);
                    EqualityFactB((gt == actualr), true, $"Control 1: Expected {gt}, got {actualr}");

                    ResetAll(controls);
                }
            }
        }
    }
	operation LessThanConstantLookAheadExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..7) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    LessThanConstantTestHelper(LessThanConstantLookAhead,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

	operation LessThanConstantLookAheadExhaustiveTest () : Unit {
        for (numberOfQubits in 1..5) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    LessThanConstantTestHelper(LessThanConstantLookAhead,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

    operation LessThanConstantExhaustiveReversibleTest () : Unit {
        for (numberOfQubits in 1..7) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    LessThanConstantTestHelper(LessThanConstant,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

    operation LessThanConstantExhaustiveTest () : Unit {
        for (numberOfQubits in 1..5) {
            for (integer1 in 0..2^numberOfQubits-1) {
                for (integer2 in 0..2^numberOfQubits-1) {
                    LessThanConstantTestHelper(LessThanConstant,IntAsBigInt(integer1), IntAsBigInt(integer2), numberOfQubits);
                }
            }
        }
    }

}
