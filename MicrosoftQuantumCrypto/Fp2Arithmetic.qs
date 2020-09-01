// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Fp2Arithmetic {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Microsoft.Quantum.Crypto.Arithmetic;


    ///////////////////////////////////////////////////////////////////////////////////////////////
    //////                                                                                  ///////
    //////                              Fp2 Arithmetic                                      ///////
    //////                                                                                  ///////
    ///////////////////////////////////////////////////////////////////////////////////////////////


    /// # Summary
    /// Type to represent a quantum element of $F_{p^2}$, the quadratic extension
    /// of a finite field over a prime, represented in Montgomery form.
    ///
    /// # Elements
    /// ## reals
    /// Qubit register encoding the real part in Montgomery form.
    /// ## imags
    /// Qubit register encoding the imaginary part in Montgomery Form.
    /// ## modulus
    /// The modulus p of the base field
    newtype Fp2MontModInt = (modulus : BigInt, reals : MontModInt, imags : MontModInt);

    /// # Summary
    /// Type to represent a classical element of $F_{p^2}$, the quadratic extension
    /// of a finite field over a prime.
    ///
    /// # Elements
    /// ## real
    /// The real part of the element.
    /// ## imags
    /// The imaginary part of the element.
    /// ## modulus
    /// The modulus p of the base field
    newtype Fp2ElementClassical = (modulus : BigInt, real : BigInt, imag : BigInt);

    /// # Summary
    /// Returns a random big integer congruent to 3 mod 4,
    /// such that (most) $F_{p^2}$ operations will function
    /// correctly with this modulus
    ///
    /// # Inputs
    /// ## nBits
    /// The bit size of the modulus. The random modulus
    /// will have any size with nBits bits
    ///
    /// # Outputs
    /// ## BigInt
    /// The random modulus
    operation RandomFp2Modulus (nBits : Int) : BigInt {
        let randomBigInt = RandomBoundedBigInt(2L^(nBits - 3), 2L^(nBits - 2));
        return 4L * randomBigInt + 3L;
    }

    /// # Summary
    /// Returns a random element of $F_{p^2}$ over a given
    /// modulus p
    ///
    /// # Inputs
    /// ## modulus
    /// The modulus p of $F_{p^2}$
    ///
    /// # Output
    /// ## Fp2ElementClassical
    /// Random $F_{p^2}$ element
    operation RandomFp2ElementClassical(modulus : BigInt) : Fp2ElementClassical {
        let real = RandomBigInt(modulus);
        let imag = RandomBigInt(modulus);
        return Fp2ElementClassical(modulus, real, imag);
    }

    /// # Summary
    /// Tests if two classical elements of $F_{p^2}$ are equal.
    /// For inputs a+bi in $F_{p^2}$ and $c+di$ in $F_{q^2}$, 
    /// returns true if and only if a=c and b=d and p=q.
    ///
    /// # Inputs
    /// ## element1
    /// Fp2ElementClassical for comparison.
    /// ## element2
    /// Fp2ElementClassical for comparison.
    function IsEqualFp2Element(element1 : Fp2ElementClassical, element2 : Fp2ElementClassical) : Bool {
        return (
            (element1::real==element2::real) and
            (element1::imag==element2::imag) and
            (element1::modulus==element2::modulus)
        );	
    }

    /// # Summary
    /// Returns a random element of $F_{p^2}$ whose inverse exists,
    /// even in cases where the modulus $p$ is composite. 
    ///
    /// # Inputs
    /// ## modulus
    /// The modulus p of $F_{p^2}$
    ///
    /// # Output
    /// ## Fp2ElementClassical
    /// Random $F_{p^2}$ element
    operation RandomInvertibleFp2ElementClassical(modulus : BigInt) : Fp2ElementClassical {
        let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
        mutable randomElement = zeroFp2;
        mutable randomNorm = 0L;
        repeat {
            set randomElement = RandomFp2ElementClassical(modulus);
            set randomNorm = (randomElement::real ^ 2 + randomElement::imag ^ 2) % modulus;
        } until (
            not IsEqualFp2Element(zeroFp2, randomElement)
            and GreatestCommonDivisorL(randomNorm, modulus) == 1L);
        return randomElement;
    }

    /// # Summary
    /// Given two classical elements of $F_{p^2}$, returns their sum.
    /// The inputs are represented as (a+bi) and (c+di), and the output
    /// is ((a+c)+(b+d)i)
    ///
    /// # Inputs
    /// ## x
    /// The first summand.
    /// ## y
    /// The second summand.
    ///
    /// # Outputs
    /// ## Fp2Elementclassical
    /// The sum.
    function AddFp2ElementClassical(x : Fp2ElementClassical, y : Fp2ElementClassical) : Fp2ElementClassical {
        let realval = (x::real + y::real) % x::modulus;
        let imagval = (y::imag + x::imag) % x::modulus;
        return Fp2ElementClassical(x::modulus, realval, imagval);
    }

    /// # Summary
    /// Given two classical elements of $F_{p^2}$, returns their difference.
    /// The inputs are represented as (a+bi) and (c+di), and the output
    /// is ((a-c)+(b-d)i)
    ///
    /// # Inputs
    /// ## x
    /// Fp2ElementClassical containing $a+bi$
    /// ## y
    /// Fp2ElementClassical containing $c+di$
    ///
    /// # Outputs
    /// ## Fp2Elementclassical
    /// The difference.
    function SubtractFp2ElementClassical(x : Fp2ElementClassical, y : Fp2ElementClassical) : Fp2ElementClassical {
        mutable realval = (x::real - y::real) % x::modulus;
        mutable imagval = (x::imag - y::imag) % x::modulus;
        if (realval < 0L){
            set realval = realval + x::modulus;
        }
        if (imagval < 0L){
            set imagval = imagval + x::modulus;
        }
        return Fp2ElementClassical(x::modulus, realval, imagval);
    }

    /// # Summary
    /// Given two classical elements of $F_{p^2}$, returns their product.
    /// The inputs are represented as (a+bi) and (c+di), and the output
    /// is ((ac-bd)+(ad+bc)i)
    ///
    /// # Inputs
    /// ## x
    /// The first multiplicand.
    /// ## y
    /// The second multiplicand.
    ///
    /// # Outputs
    /// ## Fp2Elementclassical
    /// The product.
    function MultiplyFp2ElementClassical(x : Fp2ElementClassical, y : Fp2ElementClassical) : Fp2ElementClassical {
        mutable realval = (x::real * y::real - x::imag * y::imag) % x::modulus;
        if (realval < 0L){
            set realval = realval + x::modulus;
        }
        let imagval = (x::real * y::imag + x::imag * y::real) % x::modulus;
        return Fp2ElementClassical(x::modulus, realval, imagval);
    }

    /// # Summary
    /// Squares a classical element $(a+bi)$ of $F_{p^2}$, 
    // returning $((a^2-b^2)+2abi)$. 
    ///
    /// # Inputs
    /// ## abs
    /// Classical $F_{p^2}$ element that will be squared.
    ///
    /// # Output
    /// ## Fp2ElementClassical
    /// The square of `ab`.
    function SquareFp2ElementClassical(ab : Fp2ElementClassical) : Fp2ElementClassical{
        mutable real = (ab::real^2 - ab::imag^2) % ab::modulus;
        let imag = (2L * ab::real * ab::imag) % ab::modulus;
        if (real < 0L){
            set real = real+ab::modulus;
        }
        return Fp2ElementClassical(ab::modulus, real, imag);
    }

    /// # Summary
    /// Given a classical elements of $F_{p^2}$, returns its inverse.
    /// The inputs are represented as (a+bi) and the output is
    /// is $(\frac{a}{a^2+b^2}+\frac{-b}{a^2+b^2}i)$.
    ///
    /// # Inputs
    /// ## input
    /// Element to be inverted.
    ///
    /// # Outputs
    /// ## Fp2Elementclassical
    /// The inverse.
    function InvertFp2ElementClassical(input : Fp2ElementClassical) : Fp2ElementClassical {
        mutable norm = (input::real ^ 2 + input::imag ^ 2) % input::modulus;
        Fact(not (norm==0L), $"Cannot invert ({input::real}, {input::imag}); has no inverse");
        let norminv = InverseModL(norm, input::modulus);
        let real = (input::real*norminv) % input::modulus;
        let imag = (input::modulus - ((input::imag * norminv) % input::modulus)) % input::modulus;
        return Fp2ElementClassical(input::modulus, real, imag);
    }

    /// # Summary
    /// Given a classical element of $F_{p^2}$, encodes it in Montgomery Form into two qubit registers, 
    /// and returns an Fp2MontModInt type that points to the registers.
    ///
    /// # Inputs
    /// ## value
    /// The classical $F_{p^2}$ element to be encoded.
    /// ## register
    /// Qubit register that will contain the $F_{p^2}$ element.
    ///
    /// # Output
    /// ## Fp2MontModInt
    /// Type that points to the qubit register and contains the modulus of `value`.
    ///
    /// # Remarks
    /// Fp2MontModInt types have two separate qubit registers internally, one for the real
    /// component and another for the imaginary component. Internally, this function divides
    /// the qubits in `register` for these to roles.
    operation CreateFp2MontModInt(value : Fp2ElementClassical, register : Qubit[]) : Fp2MontModInt{
        Fact(value::modulus % 4L == 3L, 
            $"Cannot create a quadratic extension over Z/{value::modulus}Z because it is not congruent to 3 mod 4."
            );
        let nQubits = BitSizeL(value::modulus);
        Fact(Length(register)>= nQubits*2,
            $"Needs {2*nQubits} qubits to encode integers modulo {value::modulus};
            only {Length(register)} given");
        let reals = LittleEndian(register[0..nQubits - 1]);
        let imags = LittleEndian(register[nQubits..2*nQubits-1]);
        return Fp2MontModInt(
            value::modulus,
            CreateBigIntInMontgomeryForm(value::modulus, value::real, reals), 
            CreateBigIntInMontgomeryForm(value::modulus, value::imag, imags)
        );
    }

    /// # Summary
    /// Encodes a classical element of $F_{p^2}$ into a blank qubit register
    /// that is already formatted as the right type.
    ///
    /// # Inputs
    /// ## value
    /// The classical element of $F_{p^2}$
    /// ## register
    /// A blank qubit register 
    operation EncodeFp2MontModInt(value : Fp2ElementClassical, register : Fp2MontModInt) : Unit {
        body (...){
            Fact(value::modulus==register::modulus, "Cannot encode {value} into 
                qubit register already initialized with a distinct modulus {register::modulus}");
            EncodeBigIntInMontgomeryForm(value::real, register::reals);
            EncodeBigIntInMontgomeryForm(value::imag, register::imags);
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Formats a qubit register as an Fp2MontModInt.
    ///
    /// # Inputs
    /// ## modulus
    /// The modulus p in $F_{p^2}$.
    /// ## register
    /// Qubit register to store element of $F_{p^2}$
    /// 
    /// # Output
    /// ## Fp2MontModInt
    /// A tuple containing the modulus and points to the qubit register.
    /// 
    /// # Remarks
    /// This differs from `EncodeFp2MontModInt` and `CreateFp2MontModInt` in that
    /// this function does not modify the qubit register in any way, it simply
    /// formats pointers to the array.
    function QubitArrayAsFp2MontModInt(modulus : BigInt, register : Qubit[]): Fp2MontModInt {
        let nQubits = BitSizeL(modulus);
        AssertEnoughQubits(2 * nQubits, "Qubit Array as Fp2MontModInt: ", register);
        return Fp2MontModInt(modulus,
            MontModInt(modulus, LittleEndian(register[0..nQubits - 1])),
            MontModInt(modulus, LittleEndian(register[nQubits .. 2 * nQubits - 1]))
        );
    }


    /// # Summary
    /// Measures the quantum registers of an element of $F_{p^2}$ in Montgomery form
    /// and returns the value as a classical element of $F_{p^2}$.
    ///
    /// # Inputs
    /// ## quantumvalue
    /// Qubit register containing an element of $F_{p^2}$.
    ///
    /// # Output
    /// ## Fp2ElementClassical
    /// The values measured from `quantumvalue`, returned in normal (not Montgomery)
    /// form.
    ///
    /// # Remarks
    /// This function resets the value in the qubit registers to 0.
    operation MeasureFp2MontModInt(quantumValue : Fp2MontModInt) : Fp2ElementClassical {
        return Fp2ElementClassical(
            quantumValue::modulus,
            MeasureMontgomeryInteger(quantumValue::reals), 
            MeasureMontgomeryInteger(quantumValue::imags)
        );
    }
    


    /// # Summary
    /// In-place negation of an element of $F_{p^2}$, 
    /// encoded in Montgomery form in qubit registers.
    /// Sends (a+bi) to (-a-bi).
    ///
    /// # Inputs
    /// ## xs
    /// Fp2MontModInt which will be returned negated.
    ///
    /// # Remarks
    /// When controlled, it copies the control to 2 ancilla
    /// to parallelize.
    operation NegFp2MontgomeryForm(abs : Fp2MontModInt) : Unit {
        body (...){
            ModularNegMontgomeryForm(abs::reals);
            ModularNegMontgomeryForm(abs::imags);
        }
            controlled (controls, ...){
            using (singleControls = Qubit[2]){
                (Controlled X)(controls, (singleControls[0]));
                CNOT(singleControls[0], singleControls[1]);
                (Controlled ModularNegMontgomeryForm)([singleControls[0]], (abs::reals));
                (Controlled ModularNegMontgomeryForm)([singleControls[1]], (abs::imags));
                CNOT(singleControls[0], singleControls[1]);
                (Controlled X)(controls, (singleControls[0]));
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// In-place conjugation of an element of $F_{p^2}$, 
    /// encoded in Montgomery form in qubit registers.
    /// Sends (a+bi) to (a-bi)
    ///
    /// # Inputs
    /// ## xs
    /// Fp2MontModInt which will be conjugated.
    operation ConjugateFp2MontgomeryForm(abs : Fp2MontModInt) : Unit {
        body (...){
            ModularNegMontgomeryForm(abs::imags);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// In-place doubling of an element of $F_{p^2}$, 
    /// encoded in Montgomery form in qubit registers.
    /// Sends (a+bi) to (2a+2bi), modulo the prime
    /// p contained in the input tuple.
    ///
    /// # Inputs
    /// ## abs
    /// Fp2MontModInt which will be doubled.
    ///
    /// # Remarks
    /// When controlled, it copies the control to 2 ancilla
    /// to parallelize.
    operation DblFp2MontgomeryForm(abs : Fp2MontModInt) : Unit {
        body (...){
            ModularDblMontgomeryForm(abs::reals);
            ModularDblMontgomeryForm(abs::imags);
        }
        controlled (controls, ...){
            using (singleControls = Qubit[2]){
                (Controlled X)(controls, (singleControls[0]));
                CNOT(singleControls[0], singleControls[1]);
                (Controlled ModularDblMontgomeryForm)([singleControls[0]], (abs::reals));
                (Controlled ModularDblMontgomeryForm)([singleControls[1]], (abs::imags));
                CNOT(singleControls[0], singleControls[1]);
                (Controlled X)(controls, (singleControls[0]));
            }
        }
        adjoint controlled auto;
    }



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
    operation AddFp2ElementMontgomeryForm(abs : Fp2MontModInt, cds : Fp2MontModInt) : Unit {
        body (...){
            (Controlled AddFp2ElementMontgomeryForm)(new Qubit[0], (abs, cds));
        }
        controlled (controls, ...){
            (Controlled ModularAddMontgomeryForm)(controls, (abs::reals, cds::reals));
            (Controlled ModularAddMontgomeryForm)(controls, (abs::imags, cds::imags));
        }
        adjoint controlled auto;
    }

    /// # Summary 
    /// Copies the contents of a qubit register that
    /// contains an element of $F_{p^2}$ to another
    /// register.
    ///
    /// # Inputs
    /// ## source
    /// Qubit register to copy from
    /// ## target
    /// Qubit register to copy to
    ///
    /// # Remarks
    /// Borrows a qubit to copy the controls and
    /// copy the real and imaginary components simultaneously.
    operation CopyFp2MontModInt(source : Fp2MontModInt, target : Fp2MontModInt) : Unit {
        body (...){
            CopyLittleEndian(source::reals::register, target::reals::register);
            CopyLittleEndian(source::imags::register, target::imags::register);
        }
        controlled (controls, ...){
            using (spareControl = Qubit()){
                (Controlled X)(controls, (spareControl));
                (Controlled CopyLittleEndian)(controls, (source::reals::register, target::reals::register) );
                (Controlled CopyLittleEndian)([spareControl], (source::imags::register, target::imags::register));
                (Controlled X)(controls, (spareControl));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Swaps two qubit registers containing elements
    /// of $F_{p^2}$
    ///
    /// # Inputs
    /// ## input1
    /// One qubit register with an element of $F_{p^2}$
    /// ## input2
    /// Second qubit register with an element of $F_{P^2}$
    ///
    /// # Remarks
    /// The controlled version borrows a qubit to control the
    /// swaps of the real and imaginary registers simultaneously.
    operation SwapFp2ElementMontgomeryForm(input1 : Fp2MontModInt, input2 : Fp2MontModInt) : Unit {
        body (...){
            SwapLE(input1::reals::register, input2::reals::register);
            SwapLE(input1::imags::register, input2::imags::register);
        }
        controlled (controls, ...){
            using (singleControl = Qubit()){
                (Controlled X)(controls, (singleControl));
                (Controlled SwapLE)(controls, (input1::reals::register, input2::reals::register));
                (Controlled SwapLE)([singleControl], (input1::imags::register, input2::imags::register));
                (Controlled X)(controls, (singleControl));
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Maps a pair x and y in $F_{p^2}$ to x-y and x+y, in place.
    ///
    /// # Inputs
    /// ## inputMinus
    /// Qubit register encoding x that is returned containing x-y.
    /// ## inputPlus
    /// Fp2MontModInt encoding y that is returned containing x+y.
    ///
    /// # Remarks
    /// If x=a+bi and y=c+di, this returns (a-c)+(b-d)i and (a+c)+(b+d)i. 
    /// That is, it "criss-crosses" the entire elements of $F_{p^2}$, not their 
    /// components.
    operation CrissCrossFp2ElementMontgomeryForm(inputMinus : Fp2MontModInt, inputPlus : Fp2MontModInt) : Unit {
        body (...){
            CrissCrossMontgomeryForm(inputMinus::reals, inputPlus::reals);
            CrissCrossMontgomeryForm(inputMinus::imags, inputPlus::imags);
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Computes the product of two quantum elements of $F_{p^2}$, XORing
    /// the result to a third element initialized to 0.
    /// The inputs are represented as (a+bi) and (c+di), and the output
    /// is ((ac-bd)+(ad+bc)i)
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register containing the first element, a+bi.
    /// ## cds
    /// Qubit register containing the second element, c+di.
    /// ## blankOutputs
    /// Qubit register initialized to 0 which will contain the product.
    /// 
    /// # Remarks
    /// The behaviour is undefined for `blankOutputs` not equal to 0+0i.
    /// This saves roughly 6 additions compared to addition into `blankOutputs`	
    operation MulAndXorFp2ElementMontgomeryForm(abs : Fp2MontModInt, cds : Fp2MontModInt, blankOutputs : Fp2MontModInt) : Unit {
        body(...){
            (Controlled MulAndXorFp2ElementMontgomeryForm)(new Qubit[0], (abs, cds, blankOutputs));
        }
        controlled (controls, ...){
            // Given input (a+bi) and (c+di)
            // Set to ((a+b)+(b-a)i) and ((c+d)+(d-c)i)
            CrissCrossMontgomeryForm(abs::imags, abs::reals);
            CrissCrossMontgomeryForm(cds::imags, cds::reals);
             //This produces
             // (ac-ad-bc+bd)+(ac+ad+bc+bd)i
             // in the output register
             (Controlled ModularMulAndXorMontgomeryForm)(controls, (abs::reals, cds::reals, blankOutputs::imags));
             (Controlled ModularMulAndXorMontgomeryForm)(controls, (abs::imags, cds::imags, blankOutputs::reals));
             //Restores input to ((a+b)+bi) and ((c+d)+2di)
             ModularAddMontgomeryForm(cds::reals, cds::imags);
             ModularAddMontgomeryForm(abs::reals, abs::imags);
             (Adjoint ModularDblMontgomeryForm)(abs::imags);
             //Fixes output to
             // (ac+bd)+(ad+bc)i
             (Adjoint CrissCrossMontgomeryForm)(blankOutputs::reals,blankOutputs::imags);
             //Fixes output to
             // (ac-bd)+(ad+bc)i
             (Adjoint Controlled ModularMulAndAddMontgomeryForm)(controls, (abs::imags, cds::imags, blankOutputs::reals));
             //Fixes input to
             // (a+bi) and (c+di)
             (Adjoint ModularDblMontgomeryForm)(cds::imags);
             (Adjoint ModularAddMontgomeryForm)(abs::imags, abs::reals);
             (Adjoint ModularAddMontgomeryForm)(cds::imags, cds::reals);
        }
        controlled adjoint auto;
    }

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
    operation MulAndAddFp2ElementMontgomeryForm(abs : Fp2MontModInt, cds : Fp2MontModInt, outputs : Fp2MontModInt) : Unit {
        body(...){
            (Controlled MulAndAddFp2ElementMontgomeryForm)(new Qubit[0], (abs, cds, outputs));
        }
        controlled (controls, ...){		
            // Given output x+yi
            //Sets output to (x-y)+(x+y)i
            CrissCrossMontgomeryForm(outputs::reals, outputs::imags);
            
            // Given input (a+bi) and (c+di)
            // Set to ((a+b)+(b-a)i) and ((c+d)+(d-c)i)
            CrissCrossMontgomeryForm(abs::imags, abs::reals);
            CrissCrossMontgomeryForm(cds::imags, cds::reals);
             //This produces
             // (x-y+ac-ad-bc+bd)+(x+y+ac+ad+bc+dd)i
             // in the output register
             (Controlled ModularMulAndAddMontgomeryForm)(controls, (abs::reals, cds::reals, outputs::imags));
             (Controlled ModularMulAndAddMontgomeryForm)(controls, (abs::imags, cds::imags, outputs::reals));
             //Restores input to ((a+b)+bi) and ((c+d)+2di)
             ModularAddMontgomeryForm(cds::reals, cds::imags);
             ModularAddMontgomeryForm(abs::reals, abs::imags);
             (Adjoint ModularDblMontgomeryForm)(abs::imags);
             //Fixes output to
             // (x+ac+bd)+(y+ad+bc)i
             (Adjoint CrissCrossMontgomeryForm)(outputs::reals, outputs::imags);
             //Fixes output to
             // (x+ac-bd)+(y+ad+bc)i
             (Adjoint Controlled ModularMulAndAddMontgomeryForm)(controls, (abs::imags, cds::imags, outputs::reals));
             //Fixes input to
             // (a+bi) and (c+di)
             (Adjoint ModularDblMontgomeryForm)(cds::imags);
             (Adjoint ModularAddMontgomeryForm)(abs::imags, abs::reals);
             (Adjoint ModularAddMontgomeryForm)(cds::imags, cds::reals);
        }
        controlled adjoint auto;
    }

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
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation MulFp2ElementMontgomeryFormOpen(abs : Fp2MontModInt, cds : Fp2MontModInt, ancillas : Qubit[], blankOutputs : Fp2MontModInt) : Unit {
        body(...){

            // Given input (a+bi) and (c+di)
            // Set to ((a+b)+(b-a)i) and ((c+d)+(d-c)i)
            CrissCrossMontgomeryForm(abs::imags, abs::reals);
            CrissCrossMontgomeryForm(cds::imags, cds::reals);

            //Ancilla bookkeeping
            let nQubits = Length(abs::reals::register!);
            let (nSelfAncilla,_) = AncillaCountFp2MulMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Fp2 multiplication:", ancillas);
            let (nMulAncilla,nMulOutput) = AncillaCountModularMulMontgomeryForm(nQubits);
            let multiplicationAncillas = [
                ancillas[0 .. nMulAncilla - 1],
                ancillas[nMulAncilla .. 2 * nMulAncilla - 1],
                ancillas[2 * nMulAncilla .. 3 * nMulAncilla - 1]
            ];
             
            let modulus = abs::reals::modulus;
            let multiplicationOutputs = [
                MontModInt(modulus,LittleEndian(ancillas[3 * nMulAncilla .. 3 * nMulAncilla + nMulOutput - 1]))
            ];
            //This produces
            // (ac-ad-bc+bd)+(ac+ad+bc+dd)i
            // in the output register
            ModularMulMontgomeryFormOpen(abs::reals, cds::reals, multiplicationAncillas[0], blankOutputs::imags);
            ModularMulMontgomeryFormOpen (abs::imags, cds::imags,  multiplicationAncillas[1], blankOutputs::reals);
            //Restores input to ((a+b)+bi) and ((c+d)+2di)
            ModularAddMontgomeryForm(cds::reals, cds::imags);
            ModularAddMontgomeryForm(abs::reals, abs::imags);
            (Adjoint ModularDblMontgomeryForm)(abs::imags);
            //Fixes output to
            // (ac+bd)+(ad+bc)i
            (Adjoint CrissCrossMontgomeryForm)(blankOutputs::reals, blankOutputs::imags);
            //Fixes output to
            // (ac-bd)+(ad+bc)i
            ModularMulMontgomeryFormOpen(abs::imags, cds::imags,  multiplicationAncillas[2], multiplicationOutputs[0]);
            (Adjoint ModularAddMontgomeryForm)(multiplicationOutputs[0], blankOutputs::reals);
            //Fixes input to
            // (a+bi) and (c+di)
            (Adjoint ModularDblMontgomeryForm)(cds::imags);
            (Adjoint ModularAddMontgomeryForm)(abs::imags, abs::reals);
            (Adjoint ModularAddMontgomeryForm)(cds::imags, cds::reals);
        }
        controlled adjoint auto;
    }
    
    /// # Summary
    /// Returns the number of ancilla necessary for an open multiplication
    /// of elements of Fp2
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the integers being multiplied
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountFp2MulMontgomeryForm (nQubits : Int) : (Int, Int) {
        let (nMulAncilla,nMulOutput) = AncillaCountModularMulMontgomeryForm(nQubits);
        return (3 * nMulAncilla + nMulOutput, 2 * nQubits);
    }

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
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation MulByConstantFp2MontgomeryFormOpen(constant : Fp2ElementClassical, abs : Fp2MontModInt, ancillas : Qubit[], blankOutputs : Fp2MontModInt) : Unit {
        body (...){
            let nQubits = Length(abs::reals::register!);
            let constantCrossPlus = (constant::real + constant::imag) % constant::modulus;
            let constantCrossMinus = (constant::modulus + constant::imag - constant::real) % constant::modulus;
            let modulus = abs::modulus;
            let (nTotalAncillas, nSelfMulOutputs) = AncillaCountFp2MulConstantMontgomeryForm(nQubits);
            AssertEnoughQubits(nTotalAncillas, "Multiply by constant in Fp2 ancilla: ", ancillas);
            //Ancilla bookkeeping
            let (nMulAncillas, nMulOutputs) = AncillaCountConstantMulMontgomeryForm(nQubits);
            let mulAncillas = [
                ancillas[0 .. nMulAncillas - 1],
                ancillas[nMulAncillas .. 2 * nMulAncillas - 1],
                ancillas[2 * nMulAncillas .. 3 * nMulAncillas - 1]
            ];
            let nSelfAncillas = 3 * nMulAncillas;
            let mulOutputs = [
                MontModInt(modulus, LittleEndian(ancillas[nSelfAncillas .. nSelfAncillas + nMulOutputs - 1]))
            ];
            // Given input (a+bi) and (c+di)
            // Set to ((a+b)+(b-a)i) and ((c+d)+(d-c)i)
            CrissCrossMontgomeryForm(abs::imags, abs::reals);
            //This produces
            // (ac-ad-bc+bd)+(ac+ad+bc+dd)i
            // in the output register
            MulByConstantMontgomeryFormOpen (constantCrossPlus, abs::reals, mulAncillas[0], blankOutputs::imags);
            MulByConstantMontgomeryFormOpen (constantCrossMinus, abs::imags, mulAncillas[1], blankOutputs::reals);
            ModularAddMontgomeryForm(abs::reals, abs::imags);
            //Fixes output to
            // (ac+bd)+(ad+bc)i
            (Adjoint CrissCrossMontgomeryForm)(blankOutputs::reals, blankOutputs::imags);
    
            MulByConstantMontgomeryFormOpen(constant::imag, abs::imags,  mulAncillas[2], mulOutputs[0]);
            (Adjoint ModularAddMontgomeryForm)(mulOutputs[0], blankOutputs::reals);
            //Fixes inputs
            (Adjoint ModularDblMontgomeryForm)(abs::imags);
            (Adjoint ModularAddMontgomeryForm)(abs::imags, abs::reals);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open multiplication
    /// of a quantum and classical element of Fp2
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the integers being multiplied
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountFp2MulConstantMontgomeryForm (nQubits : Int) : (Int, Int) {
        let (nMulAncilla,nMulOutput) = AncillaCountConstantMulMontgomeryForm(nQubits);
        return (3 * nMulAncilla + nMulOutput, 2 * nQubits);
    }

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
    operation MulByConstantAndAddFp2MontgomeryFormGeneric(constant : Fp2ElementClassical, abs : Fp2MontModInt, outputs : Fp2MontModInt) : Unit {
        body (...){
            (Controlled MulByConstantAndAddFp2MontgomeryFormGeneric)(new Qubit[0], (constant, abs, outputs));
        }
        controlled (controls, ...){
            let nQubits = Length(abs::reals::register!);
            let constantCrossPlus = (constant::real + constant::imag) % constant::modulus;
            let constantCrossMinus = (constant::modulus + constant::imag - constant::real) % constant::modulus;
            let modulus = abs::modulus;
            // Given input (a+bi) 
            // Set to ((a+b)+(b-a)i)
            CrissCrossMontgomeryForm(abs::imags, abs::reals);

            // Given output x+yi
            //Sets output to (x-y)+(x+y)i
            CrissCrossMontgomeryForm(outputs::reals, outputs::imags);
            //This produces
            // (x-y+ac-ad-bc+bd)+(x+y+ac+ad+bc+dd)i
            // in the output register
            (Controlled MulByConstantMontgomeryFormGeneric)(controls, (ModularAddMontgomeryForm(_, outputs::imags), constantCrossPlus, abs::reals)); 
            (Controlled MulByConstantMontgomeryFormGeneric)(controls, (ModularAddMontgomeryForm(_, outputs::reals), constantCrossMinus, abs::imags)); 
            //Sets input to 
            // (a+b) + (2b)i
            ModularAddMontgomeryForm(abs::reals, abs::imags);
            //Fixes output to
            // (x+ac+bd)+(y+ad+bc)i
            (Adjoint CrissCrossMontgomeryForm)(outputs::reals, outputs::imags);
            //Sets output to
            // (x+ac-bd) + (y+ad+bc)i
            (Controlled MulByConstantMontgomeryFormGeneric)(controls, ((Adjoint ModularAddMontgomeryForm)(_, outputs::reals), constant::imag, abs::imags)); 
            //Fixes inputs
            (Adjoint ModularDblMontgomeryForm)(abs::imags);
            (Adjoint ModularAddMontgomeryForm)(abs::imags, abs::reals);
        }
    }

    /// # Summary
    /// Takes an element (a+bi) of $F_{p^2}$ encoded in 
    /// Montgomery form in qubit registers, and computes
    /// the square ((a^2-b^2)+2abi) into an output register, either
    /// adding or XORing, depending on the multiplication operator
    /// given as input.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register encoding $F_{p^2}$ element which will be squared
    /// ## absquareds
    /// Qubit register which will contain the output
    /// ## Multiplier
    /// Operation which is used to multiply internally, copying
    /// or adding the result to `absquareds`
    operation SquareFp2ElementMontgomeryFormGeneric(abs : Fp2MontModInt, absquareds : Fp2MontModInt, Multiplier : ((MontModInt, MontModInt, MontModInt)=>Unit is Ctl+Adj)) : Unit {
        body (...){
            (Controlled SquareFp2ElementMontgomeryFormGeneric)(new Qubit[0], (abs, absquareds, Multiplier));
        }
        controlled (controls, ...){
            ModularDblMontgomeryForm(abs::imags);
            (Controlled Multiplier)(controls, (abs::reals, abs::imags, absquareds::imags));
            (Adjoint ModularDblMontgomeryForm)(abs::imags);
            CrissCrossMontgomeryForm(abs::reals, abs::imags);
            (Controlled Multiplier)(controls, (abs::reals, abs::imags, absquareds::reals));
            (Adjoint CrissCrossMontgomeryForm)(abs::reals, abs::imags);
        }
        adjoint controlled auto;
    }


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
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation SquFp2ElementMontgomeryFormOpen(abs : Fp2MontModInt, ancillas : Qubit [], blankOutputs : Fp2MontModInt) : Unit {
        body (...){
            let nQubits = Length(abs::reals::register!);
            let (nSelfAncilla,_) = AncillaCountFp2SquMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Fp2 squaring:", ancillas);
            let (nMulAncilla,nMulOutput) = AncillaCountModularMulMontgomeryForm(nQubits);
            //Ancilla bookkeeping
            let multiplicationAncillas = [
                ancillas[0 .. nMulAncilla - 1],
                ancillas[nMulAncilla .. 2 * nMulAncilla - 1]
            ];
            // On input a+bi:
            //Sets blankOutputs::imags = 2ab
            ModularDblMontgomeryForm(abs::imags);
            ModularMulMontgomeryFormOpen(abs::reals, abs::imags, multiplicationAncillas[0], blankOutputs::imags);
            (Adjoint ModularDblMontgomeryForm)(abs::imags);
            // Sets inputs to (a+b) + (a-b)i
            CrissCrossMontgomeryForm(abs::reals, abs::imags);
            // Sets blankOutputs::reals = (a^2-b^2)
            ModularMulMontgomeryFormOpen(abs::reals, abs::imags, multiplicationAncillas[1], blankOutputs::reals);
            // Restores input to a+bi
            (Adjoint CrissCrossMontgomeryForm)(abs::reals, abs::imags);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open squaring
    /// of an element of Fp2
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of the integer being squared
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountFp2SquMontgomeryForm (nQubits : Int) : (Int, Int) {
        let (nMulAncilla,nMulOutput) = AncillaCountModularMulMontgomeryForm(nQubits);
        return (2 * nMulAncilla, 2 * nQubits);
    }

    /// # Summary
    /// Takes an element (a+bi) of $F_{p^2}$ encoded in 
    /// Montgomer form in qubit registers, and computes
    /// the square ((a^2-b^2)+2abi), and XORs this result
    /// into an output register.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register which will be squared
    /// ## absquareds
    /// Qubit register which will be XORed with the output
    operation SquAndXorFp2ElementMontgomeryForm(abs : Fp2MontModInt, absquareds : Fp2MontModInt) : Unit {
        body(...){
            SquareFp2ElementMontgomeryFormGeneric(abs, absquareds, ModularMulAndXorMontgomeryForm(_, _, _));
        }
        controlled adjoint auto;
    }

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
    operation SquAndAddFp2ElementMontgomeryForm(abs : Fp2MontModInt, absquareds : Fp2MontModInt) : Unit {
        body(...){
            SquareFp2ElementMontgomeryFormGeneric(abs, absquareds, ModularMulAndAddMontgomeryForm(_, _, _));
        }
        controlled adjoint auto;
    }

    
    
    /// # Summary
    /// Internal helper function for inverses over $F_{p^2}$.
    /// Given an integer input x in a qubit register, and 
    /// qubit registers encoding, (a+bi) and (c+di), 
    /// maps (c+di) to ((c+xa)+(d+xb)i).
    /// The intended use is that $x=(a^2+b^2)^{-1}$.
    ///
    /// # Inputs
    /// ## freeInputs
    /// Qubit register containing x, used as the free input
    /// when passing this operation to the inversion operation.
    /// ## abs
    /// Qubit register containing a+bi
    /// ## outputs
    /// Qubit register containing c+di, which wil be modified.
    operation _InternalMulAndAdd(freeInputs : MontModInt, abs : Fp2MontModInt, cds : Fp2MontModInt) : Unit{
        body (...){
            ModularMulAndAddMontgomeryForm(freeInputs, abs::reals, cds::reals);
            (Adjoint ModularMulAndAddMontgomeryForm)(freeInputs, abs::imags, cds::imags);
        }
        controlled (controls, ...){
            using (singleControls = Qubit[2]){
                (Controlled X)(controls, (singleControls[0]));
                CNOT(singleControls[0], singleControls[1]);
                (Controlled ModularMulAndAddMontgomeryForm)([singleControls[0]], (freeInputs, abs::reals, cds::reals));
                (Controlled Adjoint ModularMulAndAddMontgomeryForm)([singleControls[1]], (freeInputs, abs::imags, cds::imags));
                CNOT(singleControls[0], singleControls[1]);
                (Controlled X)(controls, (singleControls[0]));
            }
        }
        adjoint controlled auto;
    }


    /// # Summary
    /// Inverts an element of $F_{p^2}$ encoded in Montgomery Form
    /// in a qubit register, and adds the result to a quantum output register.
    ///
    /// # Inputs
    /// ## abs
    /// Qubit register which is inverted.
    /// ## cds
    /// Qubit register to which the inverse will be added.
    operation InvertAndAddFp2ElementMontgomeryForm(abs : Fp2MontModInt, cds : Fp2MontModInt) : Unit {
        body (...){
            (Controlled InvertAndAddFp2ElementMontgomeryForm)(new Qubit[0], (abs, cds));
        }
        controlled (controls, ...){
            let DoubleFp2WithInteger = DummyIntegerWrapper(Adjoint DblFp2MontgomeryForm, cds, _);
            let nQubits = Length(abs::reals::register!);
            using (squares = Qubit[nQubits]){
                let squaresMontgomery = MontModInt(abs::modulus, LittleEndian(squares));
                ModularSquMontgomeryFormGeneric(CopyMontModInt(_, squaresMontgomery), abs::reals);
                ModularSquMontgomeryFormGeneric(ModularAddMontgomeryForm(_, squaresMontgomery), abs::imags);
                (Controlled InvertBitShiftConstantModulusGeneric)(controls, 
                    (_InternalMulAndAdd(_, abs, cds), 
                    DoubleFp2WithInteger,
                    squaresMontgomery)
                );
                (Adjoint ModularSquMontgomeryFormGeneric)(ModularAddMontgomeryForm(_, squaresMontgomery), abs::imags);
                (Adjoint ModularSquMontgomeryFormGeneric)(CopyMontModInt(_, squaresMontgomery), abs::reals);
            }
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Internal function used for division of elements of $F_{p^2}$, 
    /// which performs all operations that require the inverse of the input's norm.
    /// 
    /// # Inputs
    /// ## xNormInvs
    /// Qubit register expected to contain $(a^2+b^2)^{-1}\mod p$. Returned unchanged.
    /// ## abs
    /// Qubit register expected to contain (a-b)+(a+b)i. 
    /// Returned as (a-b)+bi.
    /// ## cds
    /// Qubit register expected to contain (c-d)+(c+d)i.
    /// Returned as 2c+(c+d)i.
    /// #efs
    /// Qubit register expected to contain (e-f)+(e+f)i.
    /// Returned as $e+(ac+bd)/(a^2+b^2)+(f+(-bc+ad)/(a^2+b^2))i$
    ///
    /// # Remarks
    /// All of the inputs contain a factor of $2^k\mod p$ which will be 
    /// fixed as $(a^2+b^2)^{-1}$ is uncomputed.
    operation _MultiplyFp2InDivision(xNormInvs : MontModInt, abs : Fp2MontModInt, cds : Fp2MontModInt, efs : Fp2MontModInt) : Unit {
        body (...){
            (Controlled _MultiplyFp2InDivision)(new Qubit[0], (xNormInvs, abs, cds, efs));
        }
        controlled (controls, ...){
            //Input is expected to be : 
            //        abs = (a-b)+(a+b)i
            //        cds = (c-d)+(c+d)i
            //        efs = (e-f)+(e+f)i
            // xnorminvs = 1/(a^2+b^2)

            // Sets 
            // efs = (e-f+(ac-bc-ad+bd)/(a^2+b^2))+(e+f+(ac+bc+ad+bd)/(a^2+b^2))i
            (Controlled ModularMulMontgomeryFormGeneric)(controls,
                (
                    ModularMulAndAddMontgomeryForm(_, cds::reals, efs::reals),
                    xNormInvs,
                    abs::reals
                )
            );
            (Controlled ModularMulMontgomeryFormGeneric)(controls, 
                (
                    ModularMulAndAddMontgomeryForm(_, cds::imags, efs::imags),
                    xNormInvs,
                    abs::imags
                )
            );
            //Sets 
            //efs = (e+(ac+bd)/(a^2+b^2))+(f+(bc+ad)/(a^2+b^2))i
            (Adjoint CrissCrossMontgomeryForm)(efs::reals, efs::imags);
            // Sets abs = (a-b)+bi and cds=2c+(c+d)i
            (Adjoint ModularAddMontgomeryForm)(abs::reals, abs::imags);
            ModularAddMontgomeryForm(cds::imags, cds::reals);
            (Adjoint ModularDblMontgomeryForm)(abs::imags);
            // Subtracts 2bc/(a^2+b^2) from the imaginary component of zs
            // This completes the division, and the input must be cleaned up
            (Controlled ModularMulMontgomeryFormGeneric)(controls, 
                (
                    (Adjoint ModularMulAndAddMontgomeryForm)(_, cds::reals, efs::imags),
                    xNormInvs,
                    abs::imags
                )
            );
        }
        controlled adjoint auto;
    }


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
    /// # Remarks
    /// Currently parameterized for a high-width low-depth approach, where it 
    /// keeps the ancilla from the inversion steps while it computes the rest.
    operation DivideAndAddFp2ElementMontgomeryForm(abs : Fp2MontModInt, cds : Fp2MontModInt, efs : Fp2MontModInt) : Unit {
        body (...){
            (Controlled DivideAndAddFp2ElementMontgomeryForm)(new Qubit[0], (abs, cds, efs));
        }
        controlled (controls, ...){
            let nQubits = Length(abs::reals::register!);
            let DoubleFp2WithInteger = DummyIntegerWrapper(Adjoint DblFp2MontgomeryForm, efs, _);
            using (squares = Qubit[nQubits]){
                //Given abs = a+bi
                //	    cds = c+di
                //      efs = e+fi
                let squaresMontgomery = MontModInt(abs::modulus, LittleEndian(squares));
                //Sets the squares register to a^2+b^2
                ModularSquMontgomeryFormGeneric(CopyMontModInt(_, squaresMontgomery), abs::reals);
                ModularSquMontgomeryFormGeneric(ModularAddMontgomeryForm(_, squaresMontgomery), abs::imags);
                //Sets abs = (a-b)+(a+b)i
                //     cds = (c-d)+(c+d)i
                //     efs = (e-f)+(e+f)i
                CrissCrossMontgomeryForm(abs::reals, abs::imags);
                CrissCrossMontgomeryForm(cds::reals, cds::imags);
                CrissCrossMontgomeryForm(efs::reals, efs::imags);
                //Sets 
                (Controlled InvertBitShiftConstantModulusGeneric)(controls, (
                    _MultiplyFp2InDivision(_, abs, cds, efs), 
                    DoubleFp2WithInteger,
                    squaresMontgomery
                ));
                // Here we expect efs = (e+fi)+(c+di)(a+bi)^{-1} 
                // abs = (a-b)+bi
                // cds = 2c+(c+d)i

                //Fixes input to abs=a+bi and cds=c+di
                ModularAddMontgomeryForm(abs::imags, abs::reals);
                (Adjoint ModularDblMontgomeryForm)(cds::reals);
                (Adjoint ModularAddMontgomeryForm)(cds::reals, cds::imags);
                //Uncomputes the a^2+b^2 register
                (Adjoint ModularSquMontgomeryFormGeneric)(ModularAddMontgomeryForm(_, squaresMontgomery), abs::imags);
                (Adjoint ModularSquMontgomeryFormGeneric)(CopyMontModInt(_, squaresMontgomery), abs::reals);
            }
        }
    }

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
    /// # Remarks
    /// As with all open operations, the adjoint and controlled adjoint require
    /// the ancillas an outputs corresponding to the input. With other ancilla
    /// or outputs, the behaviour is undefined and will likely cause an exception.
    operation InvFp2ElementMontgomeryFormOpen(abs : Fp2MontModInt, ancillas : Qubit[], blankOutputs : Fp2MontModInt) : Unit {
        body (...) {
            let nQubits = Length(abs::reals::register!);
            let modulus = abs::modulus;
            let logn = BitSizeI(nQubits);
            let (nSelfAncilla, _) = AncillaCountFp2InvMontgomeryForm(nQubits);
            AssertEnoughQubits(nSelfAncilla, "Fp2 Inverse ancilla:", ancillas);
            let (nMulAncilla, nMulOutput) = AncillaCountModularMulMontgomeryForm(nQubits);
            let (nSquAncilla, nSquOutput) = AncillaCountModularSquMontgomeryForm(nQubits);
            let (nInvAncilla, nInvOutput) = AncillaCountModularInvMontgomeryForm(nQubits);

            //Ancilla bookkeeping
            let squareAncillas = [
                ancillas[0 .. nSquAncilla - 1],
                ancillas[nSquAncilla .. 2 * nSquAncilla - 1]
            ];
            let inverseAncillas = [
                ancillas[2 * nSquAncilla .. 2 * nSquAncilla + nInvAncilla - 1]
            ];
            let multiplyAncillas = [				
                ancillas[2 * nSquAncilla + nInvAncilla .. 2 * nSquAncilla + nInvAncilla + nMulAncilla - 1],
                ancillas[2 * nSquAncilla + nInvAncilla + nMulAncilla .. 2 * nSquAncilla + nInvAncilla + 2 * nMulAncilla - 1]
            ];
            let nInternalAncillas = 2 * nSquAncilla + nInvAncilla + 2 * nMulAncilla;
            let squareOutputs = [
                MontModInt(modulus,LittleEndian(ancillas[nInternalAncillas .. nInternalAncillas + nSquOutput - 1])),
                MontModInt(modulus,LittleEndian(ancillas[nInternalAncillas + nSquOutput .. nInternalAncillas + 2 * nSquOutput - 1]))
            ];
            let inverseOutputs = [
                MontModInt(modulus,LittleEndian(ancillas[nInternalAncillas + 2 * nSquOutput .. nInternalAncillas + 2 * nSquOutput + nInvOutput - 1]))
            ];
            // For input a+bi:
            // Sets internalOutputs[0] = a^2+b^2
            ModularSquMontgomeryFormOpen(abs::reals, squareAncillas[0], squareOutputs[0]);
            ModularSquMontgomeryFormOpen(abs::imags, squareAncillas[1], squareOutputs[1]);
            ModularAddMontgomeryForm(squareOutputs[1],squareOutputs[0]);
            // Sets internalOutputs[2] = (a^2+b^2)^{-1}
            ModularInvMontgomeryFormOpen(squareOutputs[0], inverseAncillas[0], inverseOutputs[0]);
            // Sets blankOutputs = a/(a^2+b^2) - (b/(a^2+b^2))i
            ModularMulMontgomeryFormOpen(inverseOutputs[0], abs::reals, multiplyAncillas[0], blankOutputs::reals);
            ModularMulMontgomeryFormOpen(inverseOutputs[0], abs::imags, multiplyAncillas[1], blankOutputs::imags);
            ModularNegMontgomeryForm(blankOutputs::imags);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Returns the number of ancilla and output qubits
    /// necessary for an open modular inverse
    /// of an element of $F_{p^2}$.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits of each component 
    /// in the input element. 
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountFp2InvMontgomeryForm (nQubits : Int) : (Int, Int) {
        let (nMulAncilla, nMulOutput) = AncillaCountModularMulMontgomeryForm(nQubits);
        let (nSquAncilla, nSquOutput) = AncillaCountModularSquMontgomeryForm(nQubits);
        let (nInvAncilla, nInvOutput) = AncillaCountModularInvMontgomeryForm(nQubits);
        let nSelfAncilla = 2 * nSquAncilla + nInvAncilla + 2 * nMulAncilla +
                            2 * nSquOutput + nInvOutput;
        let nSelfOutputs = 2 * nQubits;
        return (nSelfAncilla, nSelfOutputs);
    }


    
}