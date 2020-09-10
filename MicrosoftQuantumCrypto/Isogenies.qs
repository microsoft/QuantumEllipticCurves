// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Isogenies {
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Microsoft.Quantum.Crypto.Fp2Arithmetic;



    ///////////////////////////////////////////////////////////////////////////////////////////////
    //////                                                                                  ///////
    //////                                  Isogenies                                       ///////
    //////                                                                                  ///////
    ///////////////////////////////////////////////////////////////////////////////////////////////

    /// # Summary
    /// Quantum registers encoding the projective (X:Z) coordinates of
    /// a point on an elliptic curve in Montgomery form $y^2=x^3+ax^2+x$ 
    /// over $F_{p^2}$
    /// 
    /// # Elements
    /// ## xs
    /// Qubit register containing the projective X coordinate
    /// ## zs
    /// Qubit register containing the projective Z coordinate
    newtype ECPointMontgomeryXZ = (xs : Fp2MontModInt, zs : Fp2MontModInt);

    /// # Summary
    /// Classical projective (X:Z) coordinates of a point on an elliptic curve
    /// in Montgomery form $y^2=x^3+ax^2+x$ over $F_{p^2}$
    /// 
    /// # Elements
    /// ## x
    /// Classical projective X coordinate
    /// ## z
    /// Classical projective Z coordinate
    newtype ECPointMontgomeryXZClassical = (x : Fp2ElementClassical, z : Fp2ElementClassical);

    /// # Summary
    /// Quantum registers encoding the $(A_{24}^+, C_{24})$ coordinates of
    /// the coefficients of elliptic curve in Montgomery form $y^2=x^3+ax^2+x$ 
    /// over $F_{p^2}$. 
    ///
    /// $(A_{24}^+, C_{24})=(A+2C, 4C)$, where $(A : C)$ is projectively equivalent to
    /// $(a, 1)$ for the coefficient $a$ of the curve.
    /// 
    /// # Elements
    /// ## a24Plus
    /// Fp2MontModInt register containing $A_{24}^+$
    /// ## c24
    /// Fp2MontModInt register containing $C_{24}$
    newtype ECCoordsMontgomeryFormAPlusC = (a24Plus : Fp2MontModInt, c24 : Fp2MontModInt);

    /// # Summary
    /// Quantum registers encoding the projective (A:C) coordinates of
    /// the coefficients of elliptic curve in Montgomery form $y^2=x^3+ax^2+x$ 
    /// over $F_{p^2}$. 
    ///
    /// (A:C) is projectively equivalent to
    /// (a, 1) for the coefficient a of the curve.
    /// 
    /// # Elements
    /// ## aCoeff
    /// Fp2MontModInt register containing $A$
    /// ## cCoeff
    /// Fp2MontModInt register containing $C$
    newtype ECCoordsMontgomeryFormAC = (aCoeff : Fp2MontModInt, cCoeff : Fp2MontModInt);


    /// # Summary
    /// Classical pair of $F_{p^2}$ elements representing the $(A_{24}^+, C_{24})$ 
    /// coordinates of the coefficients of elliptic curve in Montgomery form 
    /// $y^2=x^3+ax^2+x$ over $F_{p^2}$. 
    ///
    /// $(A_{24}^+, C_{24})=(A+2C, 4C)$, where $(A : C)$ is projectively equivalent to
    /// $(a, 1)$ for the coefficient $a$ of the curve.
    /// 
    /// # Elements
    /// ## a24Plus
    /// Classical element $A_{24}^+$
    /// ## c24
    /// Classical element $C_{24}$
    newtype ECCoordsMontgomeryFormAPlusCClassical =  (a24Plus : Fp2ElementClassical, c24 : Fp2ElementClassical);

    /// # Summary
    /// Classical pair of $F_{p^2}$ elements representing the projective (A:C) 
    /// coordinates of the coefficients of elliptic curve in Montgomery form 
    /// $y^2=x^3+ax^2+x$ over $F_{p^2}$. 
    ///
    /// (A:C) is projectively equivalent to
    /// (a,1) for the coefficient $a$ of the curve.
    /// 
    /// # Elements
    /// ## aCoeff
    /// Fp2ElementClassical containing A
    /// ## cCoeff
    /// Fp2ElementClassical containing C
    newtype ECCoordsMontgomeryFormACClassical =  (aCoeff : Fp2ElementClassical, cCoeff : Fp2ElementClassical);


    /// # Summary
    /// Formates a qubit register as an elliptic curve point
    /// in projective (X : Z) coordinates over a Montgomery curve
    /// over $F_{p^2}$
    ///
    /// # Inputs
    /// ## modulus
    /// The prime p in $F_{p^2}$
    /// ## nQubits
    /// The number of qubits needed to store p
    /// ## register
    /// The qubit register to contain the point
    ///
    /// # Outputs
    /// ## ECPointMontgomeryXZ
    /// Points to the qubit register and encodes the modulus
    function QubitArrayAsECPointMontgomeryXZ(modulus : BigInt, nQubits : Int, register : Qubit[]) : ECPointMontgomeryXZ{
        return ECPointMontgomeryXZ(
            QubitArrayAsFp2MontModInt(modulus, register[0 .. 2 * nQubits - 1]),
            QubitArrayAsFp2MontModInt(modulus, register[2 * nQubits .. 4 * nQubits - 1])
        );
    }

    /// # Summary
    /// Formats a qubit register into an array of 
    /// elliptic curve points in projective (X : Z)
    /// coordinates over a Montgomery curve over $F_{p^2}$
    ///
    /// # Inputs
    /// ## nPoints
    /// The number of points the array will contain
    /// ## nQubits
    /// The number of qubits needed to represent
    /// an integer mod p
    /// ## modulus
    /// The modulus p for $F_{p^2}$
    /// ## register
    /// The qubit register
    /// 
    /// # Output
    /// ## ECPointMontgomeryXZ[]
    /// The array of elliptic curve points
    function QubitArrayAsECPointArray(nPoints : Int, nQubits : Int, modulus : BigInt, register : Qubit[]) : ECPointMontgomeryXZ[] {
        Fact(Length(register) >= 4 * nQubits * nPoints, $"Not enough qubits: 
            Only {Length(register)} qubits for {nPoints} elliptic curve points of {4 * nQubits} qubits each");
        if (Length(register) > 4 * nQubits * nPoints){
            Message($"Warning, given {Length(register)} qubits to encode {nPoints} elliptic curve
                points, which only require {4 * nPoints * nQubits} qubits");
        }
        mutable pointArray = new ECPointMontgomeryXZ[nPoints];
        for (idx in 0.. nPoints - 1){
            set pointArray w/= idx <- ECPointMontgomeryXZ(
                QubitArrayAsFp2MontModInt(modulus, register[4 * idx * nQubits .. (4 * idx + 2) * nQubits - 1]),
                QubitArrayAsFp2MontModInt(modulus, register[(4 * idx + 2) * nQubits .. (4 * idx + 4) * nQubits - 1])
            );
        }
        return pointArray;
    }

    /// # Summary
    /// Initializes a qubit register to contain an the projective (X:Z) coordinates of
    /// a classical elliptic curve point. 
    ///
    /// # Inputs
    /// ## classicalPoint
    /// ECPointMontgomeryXZClassical which is encoded (in Montgomery form) in the qubit 
    /// register.
    /// ## register
    /// The qubit register, assumed to be in the 0 state, which the returned `ECPointMontgomeryXZ` 
    /// will reference. 
    ///
    /// # Output
    /// ## ECPointMontgomeryXZ
    /// Tuple which references the qubits in register.
    ///
    /// # Remarks
    /// The qubit register must have 4 times as many qubits as bits in the modulus of `classicalpoint`.
    /// The register will be internally partitioned into four components, for the real and imaginary
    /// parts of X and Z.
    operation CreateECPointMontgomeryXZ(classicalPoint : ECPointMontgomeryXZClassical, register : Qubit[]) : ECPointMontgomeryXZ {
        let nQubits = BitSizeL(classicalPoint::x::modulus);
        Fact(4 * nQubits <= Length(register), 
            $"An elliptic curve point over {classicalPoint::x::modulus} needs {4*nQubits} qubits; only {Length(register)} given"
        );
        let pointxs = CreateFp2MontModInt(classicalPoint::x, register[0..2 * nQubits - 1]);
        let pointzs = CreateFp2MontModInt(classicalPoint::z, register[2 * nQubits..4 * nQubits - 1]);
        return ECPointMontgomeryXZ(pointxs, pointzs);
    }

    /// # Summary
    /// Encodes a classical point on an elliptic curve
    /// in Montgomery form over $F_{p^2}$, represented as
    /// projective (X:Z) coordinates, into a qubit register
    /// already formatted as a point in that field.
    ///
    /// # Inputs
    /// ## classicalPoint
    /// The classical point to encode
    /// ## register
    /// A qubit register, assumed to be empty (all zeros).
    operation EncodeECPointMontgomeryXZ(classicalPoint : ECPointMontgomeryXZClassical, register : ECPointMontgomeryXZ) : Unit {
        body (...) { 
            EncodeFp2MontModInt(classicalPoint::x, register::xs);
            EncodeFp2MontModInt(classicalPoint::z, register::zs);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Encodes the coordinates of a classical elliptic curve
    /// in Montgomery form over $F_{p^2}$, represented as
    /// projective $(A_{24}^+,C_{24})$ coordinates, into a qubit register
    /// already formatted as a curve in that field.
    ///
    /// # Inputs
    /// ## classicalCurve
    /// The classical curve to encode
    /// ## register
    /// A qubit register, assumed to be empty (all zeros).
    operation EncodeECCoordsMontgomeryFormAPlusC(classicalCurve : ECCoordsMontgomeryFormAPlusCClassical, register : ECCoordsMontgomeryFormAPlusC) : Unit {
        body (...) { 
            EncodeFp2MontModInt(classicalCurve::a24Plus, register::a24Plus);
            EncodeFp2MontModInt(classicalCurve::c24, register::c24);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Measures a qubit register containing the projective (X:Z) coordinates of a
    /// point on an elliptic curve in Montgomery form, returning the result as a classical
    /// point type.
    ///
    /// # Inputs
    /// ## point
    /// ECPointMontgomeryXZ qubit registers encoding (X:Z) coordinates of a point
    /// on a Montgomery elliptic curve.
    ///
    /// # Output
    /// ## ECPointMontgmeryXZClassical
    /// Tuple of classical data representing the measured point.
    ///
    /// # Remarks
    /// This operation clears the register in `point` to all zeros
    operation MeasureECPointMontgomeryXZ(point : ECPointMontgomeryXZ) : ECPointMontgomeryXZClassical {
        let pointx = MeasureFp2MontModInt(point::xs);
        let pointy = MeasureFp2MontModInt(point::zs);
        return ECPointMontgomeryXZClassical(pointx, pointy);
    }

    /// # Summary 
    /// Initializes a qubit register to contain an the $(A_{24}^+, C_{24})$ coordinates of
    /// a classical elliptic curve in Montgomery Form, given as $(A_{24}^+, C_{24})$.
    ///
    /// # Inputs
    /// ## curve
    /// Classical $(A_{24}^+,C_{24})$ curve coordinates which will be
    /// encoded (in Montgomery form) in the qubit register.
    /// ## register
    /// The qubit register, assumed to be in the 0 state, which the returned 
    /// `ECCoordsMontgomeryFormAPlusC` will reference. 
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAPlusC
    /// Tuple which references the qubits in register.
    ///
    /// # Remarks
    /// The qubit register must have 4 times as many qubits as bits in the modulus of `curve`.
    operation CreateECCoordsMontgomeryFormAPlusC(curve : ECCoordsMontgomeryFormAPlusCClassical, register : Qubit[]) : ECCoordsMontgomeryFormAPlusC{
        let nQubits = BitSizeL(curve::a24Plus::modulus);
        Fact(4 * nQubits <= Length(register), $"Elliptic curve coefficients over {curve::a24Plus::modulus} needs {4*nQubits} qubits; only {Length(register)} given");
        let a24plus = CreateFp2MontModInt(curve::a24Plus, register[0..2 * nQubits - 1]);
        let c24 = CreateFp2MontModInt(curve::c24, register[2*nQubits..4 * nQubits - 1]);
        return ECCoordsMontgomeryFormAPlusC(a24plus, c24);
    }

    /// # Summary
    /// Measures a qubit register containing the projective $(A_{24}^+, C_{24})$ coordinates 
    /// of an elliptic curve in Montgomery form, returning the result as a classical
    /// curve type.
    ///
    /// # Inputs
    /// ## curve
    /// Qubit registers encoding the $(A_{24}^+, C_{24})$ coordinates of 
    /// a Montgomery elliptic curve.
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAPlusCClassical
    /// Tuple of classical data $(A_{24}^+, C_{24})$ representing the measured curve.
    ///
    /// # Remarks
    /// This operation clears the register in `curve` to all zeros
    operation MeasureECCoordsMontgomeryFormAPlusC(curve : ECCoordsMontgomeryFormAPlusC) : ECCoordsMontgomeryFormAPlusCClassical {
        let a24Plus = MeasureFp2MontModInt(curve::a24Plus);
        let c24 = MeasureFp2MontModInt(curve::c24);
        return ECCoordsMontgomeryFormAPlusCClassical(a24Plus, c24);
    } 

    /// # Summary
    /// Formats a qubit array as the $(A_{24}^+,C_{24})$
    /// coordinates of an elliptic curve in Montgomery form.
    ///
    /// # Inputs
    /// ## modulus
    /// The prime $p$ where the curve lies over $F_{p^2}$.
    /// ## nQubits
    /// The bit-length of p
    /// ## register
    /// The qubit array to contain the point
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAPlusC
    /// Tuple pointing to the qubit register and encoding the modulus.
    function QubitArrayAsECCoordsMontgomeryFormAPlusC (modulus : BigInt, nQubits : Int, register : Qubit[]) : ECCoordsMontgomeryFormAPlusC {
        return ECCoordsMontgomeryFormAPlusC(
            QubitArrayAsFp2MontModInt(modulus, register[0 .. 2 * nQubits - 1]),
            QubitArrayAsFp2MontModInt(modulus, register[2 * nQubits .. 4 * nQubits - 1])
        );
    }

    /// # Summary
    /// Converts the coordinates of a Montgomery curve from $(A_{24}^+, C_{24})$ to 
    /// projective $(A : C)$ coordinates, where : 
    ///    -  The curve is $y^2=x^3+ax^2+x$
    ///    -  $(A : C)$ is projectively equivalent to $(a : 1)$
    ///    -  $(A_{24}^+, C_{24})= (A+2C, 4C)$
    ///
    /// # Input
    /// ## curve
    /// Classical tuple of $(A_{24}^+, C_{24})$
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormACClassical
    /// The new coordinates (A : C)
    ///
    /// # Remarks
    /// The output is a specific element of the equivalence class $(a : 1)$, 
    /// and specifically this function returns $(4A_{24}^+ - 2C_{24}, C_{24})$.
    function MontgomeryCurveClassicalAsACFromAPlusC(curve : ECCoordsMontgomeryFormAPlusCClassical) : ECCoordsMontgomeryFormACClassical {
        //a24Plus = A + 2C, c24 = 4C
        let twoAFourC = AddFp2ElementClassical(curve::a24Plus, curve::a24Plus); //twoAFourC = 2A + 4C
        let twoA = SubtractFp2ElementClassical(twoAFourC, curve::c24); // twoA = 2A
        let fourA = AddFp2ElementClassical(twoA, twoA); // fourA = 4A
        return ECCoordsMontgomeryFormACClassical(fourA, curve::c24); // returns (4A : 4C)
    }
    
    /// # Summary 
    /// Initializes a qubit register to contain an the (A :C) coordinates of
    /// a classical elliptic curve in Montgomery Form, given as (A :C)
    ///
    /// # Inputs
    /// ## curve
    /// Classical (A :C) curve coordinates which will be
    /// encoded (in Montgomery form) in the qubit register.
    /// ## register
    /// The qubit register, assumed to be in the 0 state, which the returned 
    /// `ECCoordsMontgomeryFormAC` will reference. 
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAC
    /// Tuple which references the qubits in register.
    ///
    /// # Remarks
    /// The qubit register must have 4 times as many qubits as bits in the modulus of `curve`.
    operation CreateECCoordsMontgomeryFormAC(classicalCurve : ECCoordsMontgomeryFormACClassical, register : Qubit[]) : ECCoordsMontgomeryFormAC {
        let nQubits = BitSizeL(classicalCurve::aCoeff::modulus);
        Fact(4 * nQubits <= Length(register), 
            $"An elliptic curve over {classicalCurve::aCoeff::modulus} needs {4*nQubits} qubits; only {Length(register)} given"
        );
        let curveA = CreateFp2MontModInt(classicalCurve::aCoeff, register[0..2 * nQubits - 1]);
        let curveC = CreateFp2MontModInt(classicalCurve::cCoeff, register[2 * nQubits..4 * nQubits - 1]);
        return ECCoordsMontgomeryFormAC(curveA, curveC);
    }

    /// # Summary
    /// Encodes the coordinates of a classical elliptic curve
    /// in Montgomery form over $F_{p^2}$, represented as
    /// projective (A : C) coordinates, into a qubit register
    /// already formatted as a curve in that field.
    ///
    /// # Inputs
    /// ## classicalCurve
    /// The classical curve to encode
    /// ## register
    /// A qubit register, assumed to be empty (all zeros).
    operation EncodeECCoordsMontgomeryFormAC(classicalCurve : ECCoordsMontgomeryFormACClassical, quantumCurve : ECCoordsMontgomeryFormAC) : Unit {
        body (...){
            EncodeFp2MontModInt(classicalCurve::aCoeff, quantumCurve::aCoeff);
            EncodeFp2MontModInt(classicalCurve::cCoeff, quantumCurve::cCoeff);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Measures a qubit register containing the projective (A : C) coordinates 
    /// of an elliptic curve in Montgomery form, returning the result as a classical
    /// curve type.
    ///
    /// # Inputs
    /// ## curve
    /// Qubit registers encoding the (A : C) coordinates of 
    /// a Montgomery elliptic curve.
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormACClassical
    /// Tuple of classical data (A : C) representing the measured curve.
    ///
    /// # Remarks
    /// This operation clears the register in `curve` to all zeros
    operation MeasureECCoordsMontgomeryFormAC(curve : ECCoordsMontgomeryFormAC) : ECCoordsMontgomeryFormACClassical {
        let aCoeff = MeasureFp2MontModInt(curve::aCoeff);
        let cCoeff = MeasureFp2MontModInt(curve::cCoeff);
        return ECCoordsMontgomeryFormACClassical(aCoeff, cCoeff);
    } 

    /// # Summary
    /// Changes the qubit registers representing an elliptc curve
    /// from $(A_{24}^+,C_{24})$ coordinates to projective
    /// (A : C) coordinates. 
    /// 
    /// # Inputs
    /// ## curve
    /// Qubit registers 
    ///
    /// # Remarks
    /// After calling this operation, the original tuple `curve` will
    /// point to qubit registers that no longer contain $(A_{24}^+,C_{24})$
    /// coordinates. Thus, the original tuple should not be used after
    /// calling this operation (hence why it is internal).
    operation _ModifyECCoordsAPlusCToAC(curve : ECCoordsMontgomeryFormAPlusC) : Unit {
        body (...){
            // Start: a24Plus = A+2C, c24 = 4C
            DblFp2MontgomeryForm(curve::a24Plus); //a24Plus = 2A+4C
            (Adjoint AddFp2ElementMontgomeryForm)(curve::c24, curve::a24Plus); //24Plus = 2A
            (Adjoint DblFp2MontgomeryForm)(curve::c24); //c24 = 2C
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Transforms qubit registers containing
    /// an elliptic curve represented by $(A_{24}^+,C_{24})$ 
    /// coordinates to a projective (A : C) representation,
    /// and returns a tuple pointing to the same qubit registers.
    ///
    /// # Inputs
    /// ## curve
    /// Tuple pointing to the qubit registers
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAC
    /// Tuple pointing to the same qubit registers, whose quantum data
    /// is now in (A : C) form.
    operation ECCoordsAPlusCToAC(curve : ECCoordsMontgomeryFormAPlusC) : ECCoordsMontgomeryFormAC {
        _ModifyECCoordsAPlusCToAC(curve);
        return ECCoordsMontgomeryFormAC(curve::a24Plus, curve::c24);
    }

    /// # Summary
    /// Transforms qubit registers containing
    /// an elliptic curve represented by projective (A :C) 
    /// coordinates to a $(A_{24}^+,C_{24})$  representation,
    /// and returns a tuple pointing to the same qubit registers.
    ///
    /// # Inputs
    /// ## curve
    /// Tuple pointing to the qubit registers
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAPlusC
    /// Tuple pointing to the same qubit registers, whose quantum data
    /// is now in $(A_{24}^+,C_{24})$ form.
    operation ECCoordsACToAPlusC(curve : ECCoordsMontgomeryFormAC) : ECCoordsMontgomeryFormAPlusC {
        let newCurve = ECCoordsMontgomeryFormAPlusC(curve::aCoeff, curve::cCoeff);
        (Adjoint _ModifyECCoordsAPlusCToAC)(newCurve);
        return newCurve;
    }




    /// # Summary
    /// Constructs the coefficients of a curve that will
    /// contain a classical elliptic curve point input
    /// as $(X:Y:Z)$ coordinates.
    ///
    /// # Inputs
    /// ## pointX
    /// The projective X coordinate of the point
    /// ## pointY
    /// The projective Y coordinate of the point
    /// ## pointZ
    /// The projective Z coordinate of the point
    /// 
    /// # Outputs
    /// ## ECCoordsMontgomeryFormAPlusCClassical
    /// Coordinates $(A_{24}^+,C_{24})$, where
    /// $(A_{24}^+,C_{24})=(A+2C:4C)$, for $(A:C)$
    /// such that $(A:C)$ is projectively equivalent
    /// to $(a:1)$ for a curve $y^2=x^3+ax^2+x$.
    function MontgomeryXZCurveOfPointClassical(pointX : Fp2ElementClassical, pointY : Fp2ElementClassical, pointZ : Fp2ElementClassical) : ECCoordsMontgomeryFormAPlusCClassical {
        let t0 = SquareFp2ElementClassical(pointY); // y^2
        let t1 = MultiplyFp2ElementClassical(t0, pointZ); //zy^2
        let t2 = SquareFp2ElementClassical(pointX); // x^2
        let t3 = MultiplyFp2ElementClassical(t2, pointX); // x^3
        let t4 = SquareFp2ElementClassical(pointZ); // z^2
        let t5 = MultiplyFp2ElementClassical(t4, pointX); //xz^2
        let t6 = AddFp2ElementClassical(t1, t3); // zy^2+x^3
        let t7 = AddFp2ElementClassical(t6, t5); // zy^2 + x^3 + xz^2
        let t8 = MultiplyFp2ElementClassical(t2, pointZ); //x^2z
        let modulus = pointX::modulus;
        let norm = (t8::real ^ 2 + t8::imag ^ 2) % modulus;
        Fact(GreatestCommonDivisorL(norm, modulus) == 1L, "Cannot construct a curve
            around ({pointX} : {pointY} : {pointZ}) because x^2z is not invertible");
        let t9 = InvertFp2ElementClassical(t8); // 1/x^2z
        mutable A = MultiplyFp2ElementClassical(t8, t7); 

        let C = Fp2ElementClassical(modulus, 4L, 0L);
        set A = AddFp2ElementClassical(A, Fp2ElementClassical(modulus, 2L, 0L));
        return ECCoordsMontgomeryFormAPlusCClassical(A, C);
    }

    /// # Summary
    /// Returns the projective (A : C) coordinates of a random
    /// Montgomery curve over $F_{p^2}$ whose j-invariant exists. 
    ///
    /// # Input
    /// ## modulus
    /// Modulus p for the curve
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormACClassical
    /// Random curve
    operation RandomECCoordsMontgomeryAC(modulus : BigInt) : ECCoordsMontgomeryFormACClassical {
        let C = RandomInvertibleFp2ElementClassical(modulus);
        let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
        mutable A = zeroFp2;
        mutable testValue = zeroFp2;
        mutable CSquared = SquareFp2ElementClassical(C);
        set CSquared = AddFp2ElementClassical(CSquared, CSquared);
        set CSquared = AddFp2ElementClassical(CSquared, CSquared);
        mutable testNorm = 2L;
        repeat {
            set A = RandomFp2ElementClassical(modulus);
            let ASquared = SquareFp2ElementClassical(A);
            set testValue = SubtractFp2ElementClassical(ASquared, CSquared);
            set testNorm = (testValue::real ^ 2 + testValue::imag ^ 2) % modulus;
        } until (
            not IsEqualFp2Element(testValue, zeroFp2)
            and GreatestCommonDivisorL(testNorm, modulus) == 1L);
        return ECCoordsMontgomeryFormACClassical(A, C);
    }


    /// # Summary
    /// Returns the j-invariant of an elliptic curve over $F_{p^2}$ in Montgomery form, 
    /// given the coordinates of the curve in projective form (A : C), where
    /// (A : C) ~ (a : 1) for the curve $y^2=x^3+Ax^2+x$.
    ///
    /// # Input
    /// ## curve
    /// Classical tuple of $(A : C)$
    ///
    /// # Output
    /// ## Fp2ElementClassical
    /// The j-invariant, as an element of $F_{p^2}$
    ///
    /// # Remarks
    /// The output is the same for projectively-equivalent inputs. 
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    This function exactly follows Algorithm 9 from Appendix A.
    function JInvariantClassical(curve : ECCoordsMontgomeryFormACClassical) : Fp2ElementClassical {
        mutable j = SquareFp2ElementClassical(curve::aCoeff);	    // 1. 
        mutable t1 = SquareFp2ElementClassical(curve::cCoeff);	    // 2. 
        mutable t0 = AddFp2ElementClassical(t1, t1);				// 3. 
        set t0 = SubtractFp2ElementClassical(j, t0);			 	// 4. 
        set t0 = SubtractFp2ElementClassical(t0, t1);			    // 5. 
        set j = SubtractFp2ElementClassical(t0, t1);				// 6. 
        set t1 = SquareFp2ElementClassical(t1);					    // 7. 
        set j = MultiplyFp2ElementClassical(j, t1);				    // 8. 
        set t0 = AddFp2ElementClassical(t0, t0);					// 9. 
        set t0 = AddFp2ElementClassical(t0, t0);					// 10.
        set t1 = SquareFp2ElementClassical(t0);					    // 11.
        set t0 = MultiplyFp2ElementClassical(t0, t1);			    // 12.
        set t0 = AddFp2ElementClassical(t0, t0);					// 13.
        set t0 = AddFp2ElementClassical(t0, t0);					// 14.
        set j = InvertFp2ElementClassical(j);					    // 15.
        set j  = MultiplyFp2ElementClassical(t0, j);				// 16.
        return j;
    }


    /// # Summary
    /// Compares two classical elliptic curve points in (X : Z) coordinates
    /// and returns true if and only if both components are equal.
    ///
    /// # Inputs
    /// ## point1
    /// Classical point being compared.
    /// ## point2
    /// Classical point being compared.
    /// 
    /// # Output
    /// ## Bool
    /// Value the equality comparison.
    ///
    /// # Remarks
    /// This will return false for projectively equivalent points that do not have exactly the same value.
    /// If the two points are on different curves but have the same (X : Z) values, this will return true, 
    /// since the type `ECPointMontgomeryXZClassical` does not encode any information about the curve itself.
    function IsEqualMontgomeryXZClassical(point1 : ECPointMontgomeryXZClassical, point2 : ECPointMontgomeryXZClassical) : Bool {
        return (IsEqualFp2Element(point1::x, point2::x) and IsEqualFp2Element(point1::z, point2::z));
    }

    /// # Summary
    /// Compares two classical elliptic curve points in (X : Z) coordinates
    /// and returns true if and only if they are projectively equivalent
    ///
    /// # Inputs
    /// ## point1
    /// Classical point being compared.
    /// ## point2
    /// Classical point being compared.
    /// 
    /// # Output
    /// ## Bool
    /// Value of the equality comparison.
    function IsEquivalentMontgomeryXZClassical(point1 : ECPointMontgomeryXZClassical, point2 : ECPointMontgomeryXZClassical) : Bool {
        // If the points are equivalent, then x1z2=x2z1
        // If x1z2=x2z1, then they are equivalent unless z2!=0 and z1==0 (or vice versa)
        let x1z2 = MultiplyFp2ElementClassical(point1::x, point2::z);
        let x2z1 = MultiplyFp2ElementClassical(point2::x, point1::z);
        let zeroFp2 = Fp2ElementClassical(point1::x::modulus, 0L, 0L);
        if (IsEqualFp2Element(point1::z, zeroFp2) and not IsEqualFp2Element(point2::z, zeroFp2)){
            return false;
        } elif (IsEqualFp2Element(point2::z, zeroFp2) and not IsEqualFp2Element(point1::z, zeroFp2)){
            return false;
        }
        return IsEqualFp2Element(x1z2, x2z1);
    }

    /// # Summary
    /// Compares two classical elliptic curves in $(A_{24}^+ : C_{24}$) coordinates
    /// and returns true if and only if both components are equal.
    ///
    /// # Inputs
    /// ## curve1
    /// Classical curve being compared.
    /// ## curve2
    /// Classical curve being compared.
    /// 
    /// # Output
    /// ## Bool
    /// Value the equality comparison.
    ///
    /// # Remarks
    /// This will return false for projectively equivalent curve that do not have exactly the same value.
    function IsEqualECCoordsMontgomeryFormAPlusC(curve1 : ECCoordsMontgomeryFormAPlusCClassical, curve2 : ECCoordsMontgomeryFormAPlusCClassical) : Bool {
        return (IsEqualFp2Element(curve1::a24Plus, curve2::a24Plus) and IsEqualFp2Element(curve2::c24, curve2::c24));
    }

    /// # Summary
    /// Doubles a classical point P given as (X : Z) coordinates on a Montgomery curve.
    ///
    /// # Inputs
    /// ## point
    /// Classical point P being doubled.
    /// ## curve
    /// Classical $(A_{24}^+,C_{24})$ coordinates representing the curve which `point` is on.
    /// 
    /// # Outputs
    /// ## ECPointMontgomeryXZClassical
    /// Contains P+P.
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    This function exactly follows Algorithm 3 from Appendix A.
    function PointDoubleMontgomeryXZClassical(point : ECPointMontgomeryXZClassical, curve : ECCoordsMontgomeryFormAPlusCClassical) : ECPointMontgomeryXZClassical{
        mutable t0=SubtractFp2ElementClassical(point::x, point::z);  // 1. 
        mutable t1=AddFp2ElementClassical(point::x, point::z);       // 2.
        set t0 = SquareFp2ElementClassical(t0);                      // 3.
        set t1 = SquareFp2ElementClassical(t1);						 // 4. 
        mutable z2p = MultiplyFp2ElementClassical(curve::c24, t0);   // 5. 
        mutable x2p = MultiplyFp2ElementClassical(z2p, t1);		     // 6. 
        set t1 = SubtractFp2ElementClassical(t1, t0);				 // 7.
        set t0 = MultiplyFp2ElementClassical(curve::a24Plus, t1);    // 8.
        set z2p = AddFp2ElementClassical(z2p, t0);                   // 9.
        set z2p = MultiplyFp2ElementClassical(z2p, t1);              // 10.
        return ECPointMontgomeryXZClassical(x2p, z2p);               // 11.
    }

    /// # Summary
    /// Constructs an array of P, 2P, 4P, ...
    /// for an input point P
    ///
    /// # Inputs
    /// ## point
    /// The point P to double
    /// ## curve
    /// The curve containing P
    /// ## nPoints
    /// The number of doublings to perform
    /// (so the last point in the returned array
    /// will be 2^(nPoints - 1) * P)
    ///
    /// # Outputs
    /// ## ECPointMontgomeryXZClassical[]
    /// Array of the multiples of P: 
    /// [P, 2P, 4P, 8P, ...]
    function DoubledPointArray(point : ECPointMontgomeryXZClassical, curve : ECCoordsMontgomeryFormAPlusCClassical, nPoints : Int) : ECPointMontgomeryXZClassical[] {
        mutable points = new ECPointMontgomeryXZClassical[nPoints];
        set points w/= 0 <- point;
        for (idx in 1 .. nPoints - 1){
            set points w/= idx <- PointDoubleMontgomeryXZClassical(points[idx - 1], curve);
        }
        return points;
    }

    /// # Summary
    /// Given a point P of exact order 2 with (X : Z) != (0 : 1) on a Montgomery curve E, 
    /// returns coordinates $(A_{24}^+, C_{24})$ of the curve E' reached by the 2-isogeny with
    /// kernel generated by P.
    ///
    /// # Inputs
    /// ## point
    /// Classical point, expected to have exact order 2 and not
    /// equal to (0 : 1).
    ///
    /// # Output
    /// ## ECCoordsMontgomeryFormAPlusCClassical
    /// The isogenous curve E'
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    This function exactly follows Algorithm 11 from Appendix A, 
    ///    except step 3, which reverses the order of subtraction.
    function TwoIsogenousCurveMontgomeryXZClassical(point : ECPointMontgomeryXZClassical) : ECCoordsMontgomeryFormAPlusCClassical{
        mutable a24Plus = SquareFp2ElementClassical(point::x);         // 1.
        mutable c24 = SquareFp2ElementClassical(point::z);             // 2.
        set a24Plus = SubtractFp2ElementClassical(c24, a24Plus);       // 3.
        return ECCoordsMontgomeryFormAPlusCClassical(a24Plus, c24);    // 4.
    }

    /// # Summary
    /// Given a point P of exact order 2 with (X : Z) != (0 : 1), a point Q
    /// not equal to P, both on the same curve, returns the image of Q under
    /// the isogeny whose kernel is generated by P.
    ///
    /// # Inputs
    /// ## kernelpoint
    /// Classical point P, expected to have exact order 2 and not
    /// equal to (0 : 1).
    /// ## inputpoint
    /// Classical point Q as input to the isogeny, expected to be
    /// neither (0 : 0) nor P.
    ///
    /// # Output
    /// ## ECPointMontgomeryXZClassical
    /// The image of Q under the isogeny.
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    This function exactly follows Algorithm 12 from Appendix A.
    function TwoIsogenyAtPointMontgomeryXZClassical(kernelPoint : ECPointMontgomeryXZClassical, inputPoint : ECPointMontgomeryXZClassical) : ECPointMontgomeryXZClassical{
        mutable t0 = AddFp2ElementClassical(kernelPoint::x, kernelPoint::z);			// 1.
        mutable t1 = SubtractFp2ElementClassical(kernelPoint::x, kernelPoint::z);	    // 2.
        mutable t2 = AddFp2ElementClassical(inputPoint::x, inputPoint::z);			    // 3.
        mutable t3 = SubtractFp2ElementClassical(inputPoint::x, inputPoint::z);		    // 4.
        set t0 = MultiplyFp2ElementClassical(t0, t3);								    // 5.
        set t1 = MultiplyFp2ElementClassical(t1, t2);								    // 6.
        set t2 = AddFp2ElementClassical(t0, t1);										// 7.
        set t3 = SubtractFp2ElementClassical(t0, t1);								    // 8.
        let xq = MultiplyFp2ElementClassical(inputPoint::x, t2);						// 9.
        let zq = MultiplyFp2ElementClassical(inputPoint::z, t3);						// 10.
        return ECPointMontgomeryXZClassical(xq, zq);									// 11.
    }

    /// # Summary
    /// Given points P, Q, and Q-P in (X:Z) coordinates
    /// on a Montgomery curve, returns Q+P.
    ///
    /// # Inputs
    /// ## pointP
    /// The point P 
    /// ## point Q
    /// The point Q
    /// # pointQminP
    /// The point Q-P
    ///
    /// # Output
    /// ## ECPointMontgomeryXZClassical
    /// The sum Q+P
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    This function follows Algorithm 5 from Appendix A, except all steps
    ///    used for point doubling are not included. 
    ///
    /// # Remarks
    /// If either P or Q is the point at infinity (X:Z)=(0:0), this function
    /// simply returns Q or P (respectively).
    function DifferentialAddECPointMontgomeryXZClassical(
        pointP : ECPointMontgomeryXZClassical, 
        pointQ : ECPointMontgomeryXZClassical, 
        pointQminP : ECPointMontgomeryXZClassical
    ) : ECPointMontgomeryXZClassical {
        let zeroFp2 = Fp2ElementClassical(pointP::x::modulus,0L,0L);
        //	if (IsEqualFp2Element(pointP::x,zeroFp2) and IsEqualFp2Element(pointP::z,zeroFp2)){
        //		return pointQ;
        //	}
        //	if (IsEqualFp2Element(pointQ::x,zeroFp2) and IsEqualFp2Element(pointQ::z,zeroFp2)){
        //		return pointP;
        //	} 
        mutable  t0 = AddFp2ElementClassical(pointP::x, pointP::z);			//1
        mutable  t1 = SubtractFp2ElementClassical(pointP::x, pointP::z);	//2
        //skip (used for doubling)											//3
        mutable  t2 = SubtractFp2ElementClassical(pointQ::x, pointQ::z);	//4
        mutable xPQ = AddFp2ElementClassical(pointQ::x, pointQ::z);			//5
        set      t0 = MultiplyFp2ElementClassical(t0, t2);					//6
        //skip (used for doubling)											//7
        set      t1 = MultiplyFp2ElementClassical(t1,xPQ);					//8
        //skip (used for doubling)											//9
        //skip (used for doubling)											//10
        //skip (used for doubling)											//11
        mutable	zPQ = SubtractFp2ElementClassical(t0, t1);					//12
        //skip (used for doubling)											//13
        set		xPQ = AddFp2ElementClassical(t0, t1);						//14
        //skip (used for doubling)											//15
        set		zPQ = SquareFp2ElementClassical(zPQ);						//16
        set		xPQ = SquareFp2ElementClassical(xPQ);						//17
        set		zPQ = MultiplyFp2ElementClassical(pointQminP::x, zPQ);		//18
        set		xPQ = MultiplyFp2ElementClassical(pointQminP::z, xPQ);		//19
        return ECPointMontgomeryXZClassical(xPQ,zPQ);

    }

    /// # Summary
    /// Takes $(A_{24}^+,C_{24})$ coordinates of a Montgomery
    /// elliptic curve, points P, Q, and Q-P on this curve, 
    /// and a constant s, and returns $(2^nP,Q+sP,Q+sP-2^nP)$,
    /// where n is the number of bits in s.
    ///
    /// # Inputs
    /// ## curve
    /// Coordinates for the curve.
    /// ## pointP
    /// The point P.
    /// ## pointQ
    /// The point Q.
    /// ## pointQminP
    /// The point Q - P
    /// ## coefficient
    /// The number s
    ///
    /// # Outputs
    /// ## ECPointMontgomeryXZClassical
    /// The resut $2^nP$
    /// ## ECPointMontgomeryXZClassical
    /// The result Q+sP
    /// ## ECPointMontgomeryXZClassical
    /// The result $Q+sP-2^nP$
    ///
    /// # Reference
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    This function follows Algorithm 8 from Appendix A
    function PointLadderClassical(
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical, 
        pointQ : ECPointMontgomeryXZClassical, 
        pointQminP : ECPointMontgomeryXZClassical, 
        coefficient : BigInt) : 
        (ECPointMontgomeryXZClassical, ECPointMontgomeryXZClassical, ECPointMontgomeryXZClassical) {
        let constantArray = BigIntAsBoolArray(coefficient);
        mutable innerP = pointP;
        mutable innerQ = pointQ;
        mutable innerQminP = pointQminP;
        for (idx in 0..Length(constantArray) - 1){
            if (constantArray[idx]){
                set innerQ = DifferentialAddECPointMontgomeryXZClassical(innerP, innerQ, innerQminP);
            } else {
                set innerQminP = DifferentialAddECPointMontgomeryXZClassical(innerP, innerQminP, innerQ);
            }
            set innerP = PointDoubleMontgomeryXZClassical(innerP, curve);
        }
        return (innerP, innerQ, innerQminP);
    }

    /// # Summary
    /// Recursively computes a power-of-two isogeny
    /// whose kernel is generated by point given as 
    /// input.
    /// 
    /// # Inputs
    /// ## startingCurve 
    /// The curve which contains the starting point
    /// ## startingPoint
    /// The generator of the kernel of the isogeny
    /// ## trailingPoints
    /// An array (possibly empty) of points
    /// also on the curve, which the operation
    /// will map through the isogeny it computes.
    /// ## height
    /// The power of two that is the degree of the
    /// isogeny (equivalently, the log in base 2
    /// of the order of the starting point).
    ///
    /// # Outputs
    /// ## ECPointMontgomeryXZClassical[]
    /// The image of each point in `trailingPoints`
    /// under the action of the isogeny computed
    /// # ECCoordsMontgomeryFormAPlusCClassical
    /// The coordinates of the codomain of the isogeny
    /// compute
    ///
    /// # Remarks
    /// This follows a naive binary tree recursion strategy.
    function IsogenyTreeMiddleClassical(
        startingCurve: ECCoordsMontgomeryFormAPlusCClassical,
        startingPoint : ECPointMontgomeryXZClassical,
        trailingPoints : ECPointMontgomeryXZClassical[],
        height : Int
    ) : (ECPointMontgomeryXZClassical[], ECCoordsMontgomeryFormAPlusCClassical) {
        let nPoints = Length(trailingPoints);
        if (height==1){
            let outCurve = TwoIsogenousCurveMontgomeryXZClassical(startingPoint);
            mutable outPoints = new ECPointMontgomeryXZClassical[nPoints];
            for (idxPoint in 0..nPoints - 1){
                set outPoints w/= idxPoint <- TwoIsogenyAtPointMontgomeryXZClassical(startingPoint, trailingPoints[idxPoint]);
            }
            return (outPoints, outCurve);
        } else {
            let leftHeight = height/2;
            let rightHeight = height - leftHeight;
            mutable leftPoint = startingPoint;
            for (idxDouble in 0..rightHeight - 1){
                set leftPoint = PointDoubleMontgomeryXZClassical(leftPoint, startingCurve);
            }
            let (midPoints, midCurve) = IsogenyTreeMiddleClassical(
                startingCurve,
                leftPoint,
                [startingPoint] + trailingPoints,
                leftHeight
            );
            return IsogenyTreeMiddleClassical(
                midCurve,
                midPoints[0],
                midPoints[1..nPoints],
                rightHeight
            );
        }
    }

    /// # Summary
    /// Computes the j-invariant of the curve reached
    /// by an isogeny defined by a secret
    /// SIKE key, given classical parameters for the scheme.
    ///
    /// # Inputs
    /// ## startingCurve
    /// The initial curve for the scheme
    /// ## pointP
    /// A point of exact order 2^e such that 
    /// $[2^{e-1}]P = (0:0:1)$.
    /// ## pointQ
    /// A point of exact order 2^e such that 
    /// $[2^{e-1}]Q \neq (0:0:1)$.
    /// ## pointR
    /// The point equal to $Q - P$
    /// ## height
    /// The exponent e
    /// ## secret
    /// The secret key s,
    /// where the isogeny computed will have kernel
    /// generated by Q + sP
    ///
    /// # Output
    /// ## Fp2ElementClassical
    /// The j-invariant of the co-domain of the isogeny
    /// defined by the secret key.
    ///
    /// # Reference
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    function SIKETwoIsogenyClassical(
        startingCurve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointR : ECPointMontgomeryXZClassical,
        height : Int,
        secret : BigInt
    ) : Fp2ElementClassical {
        let (_, kernelPoint, _) = PointLadderClassical(startingCurve, pointP, pointQ, pointR, secret);
        let (_, outCurve) = IsogenyTreeMiddleClassical(
            startingCurve,
            kernelPoint,
            new ECPointMontgomeryXZClassical[0],
            height
        );
        return JInvariantClassical(MontgomeryCurveClassicalAsACFromAPlusC(outCurve));
    }

    /// # Summary 
    /// Copies the contents of a qubit register that
    /// contains an elliptic curve point in projective
    /// (X : Z) coordinates to another qubit register
    ///
    /// # Inputs
    /// ## source
    /// Qubit register to copy from
    /// ## target
    /// Qubit register to copy to
    ///
    /// # Remarks
    /// Borrows a qubit to copy the controls and
    /// copy the X and Z components simultaneously.
    operation CopyECPointMontgomeryXZ(source : ECPointMontgomeryXZ, target : ECPointMontgomeryXZ) : Unit {
        body (...){
            CopyFp2MontModInt(source::xs, target::xs);
            CopyFp2MontModInt(source::zs, target::zs);
        }
        controlled (controls, ...){
            using (spareControl = Qubit()){
                (Controlled X)(controls, (spareControl));
                (Controlled CopyFp2MontModInt)(controls, (source::xs, target::xs) );
                (Controlled CopyFp2MontModInt)([spareControl], (source::zs, target::zs));
                (Controlled X)(controls, (spareControl));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Swaps two elliptic curve points.
    ///
    /// # Inputs
    /// ## point1
    /// The first point
    /// ## point2
    /// The second point
    /// # Remarks
    /// Borrows a qubit to copy the controls and
    /// swap the X and Z components simultaneously.
    operation SwapECPointMontgomeryXZ(point1: ECPointMontgomeryXZ, point2 : ECPointMontgomeryXZ) : Unit {
        body (...){
            SwapFp2ElementMontgomeryForm(point1::xs, point2::xs);
            SwapFp2ElementMontgomeryForm(point1::zs, point2::zs);
        }
        controlled (controls, ...){
            using (singleControl = Qubit()){
                (Controlled X)(controls, (singleControl));
                (Controlled SwapFp2ElementMontgomeryForm)(controls, (point1::xs, point2::xs));
                (Controlled SwapFp2ElementMontgomeryForm)([singleControl], (point1::zs, point2::zs));
                (Controlled X)(controls, (singleControl));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Out-of-place doubling of an elliptic curve point in (X : Z) coordinates
    /// in a qubit register, on a curve given by $(A_{24}^+, C_{24})$ coordinates
    /// given in another qubit register.
    ///
    /// # Inputs
    /// ## point
    /// Qubit register encoding the (X : Z) coordinates to be doubled.
    /// ## curve
    /// Qubit register encoding the curve containing `point`, as 
    /// $(A_{24}^+,C_{24})$ coordinates.
    /// ## doublepoint
    /// Qubit register assumed to be initialized to $\ket{0}$.
    /// This registers will be returned containing the doubled point.
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 3 from Appendix A.
    operation DoubleECPointMontgomeryXZ(point : ECPointMontgomeryXZ, curve : ECCoordsMontgomeryFormAPlusC, doubledpoint : ECPointMontgomeryXZ) : Unit {
        body (...){
            (Controlled DoubleECPointMontgomeryXZ)(new Qubit[0], (point, curve, doubledpoint));
        }
        controlled (controls, ...){
            CrissCrossFp2ElementMontgomeryForm(point::xs, point::zs);
            let nQubits = Length(point::xs::reals::register!);
            let modulus = point::xs::modulus;
            using (register1 = Qubit[4 * nQubits]){
                let aSquareds = Fp2MontModInt(
                    modulus,
                    MontModInt(modulus, LittleEndian(register1[0..nQubits - 1])), 
                    MontModInt(modulus, LittleEndian(register1[nQubits..2 * nQubits - 1])) 
                );
                let bSquareds = Fp2MontModInt(
                    modulus,
                    MontModInt(modulus, LittleEndian(register1[2 * nQubits..3 * nQubits - 1])), 
                    MontModInt(modulus, LittleEndian(register1[3 * nQubits..4 * nQubits - 1])) 
                );
                // Let A:=x+z, B:=x-z
                //Sets asquareds = A^2, bsquareds = B^2
                SquareFp2ElementMontgomeryFormGeneric(point::zs, aSquareds, ModularMulAndXorMontgomeryForm(_, _, _));
                SquareFp2ElementMontgomeryFormGeneric(point::xs, bSquareds, ModularMulAndXorMontgomeryForm(_, _, _));
                using (register2 = Qubit[2 * nQubits]){
                    let cs = Fp2MontModInt(
                        modulus,
                        MontModInt(modulus, LittleEndian(register2[0..nQubits - 1])), 
                        MontModInt(modulus, LittleEndian(register2[nQubits..2 * nQubits - 1])) 
                    );
                    // Sets cs = C_24 * B^2
                    MulAndXorFp2ElementMontgomeryForm(curve::c24, bSquareds, cs);
                    // Sets the new x value = C_24 * A^2 * B^2
                    (Controlled MulAndXorFp2ElementMontgomeryForm)(controls, (aSquareds, cs, doubledpoint::xs));
                    // asquareds = A^2 - B^2
                    (Adjoint AddFp2ElementMontgomeryForm)(bSquareds, aSquareds);
                    // cs = C_24 * B^2 + A_24^+ * (A^2 - B^2)
                    MulAndAddFp2ElementMontgomeryForm(curve::a24Plus, aSquareds, cs);
                    // Finishes doubled point
                    (Controlled MulAndAddFp2ElementMontgomeryForm)(controls, (aSquareds, cs, doubledpoint::zs));
                    //Uncomputes
                    (Adjoint MulAndAddFp2ElementMontgomeryForm)(curve::a24Plus, aSquareds, cs);
                    AddFp2ElementMontgomeryForm(bSquareds, aSquareds);
                    (Adjoint MulAndXorFp2ElementMontgomeryForm)(curve::c24, bSquareds, cs);
                }//release cs
                (Adjoint SquareFp2ElementMontgomeryFormGeneric)(point::zs, aSquareds, ModularMulAndXorMontgomeryForm(_, _, _));
                (Adjoint SquareFp2ElementMontgomeryFormGeneric)(point::xs, bSquareds, ModularMulAndXorMontgomeryForm(_, _, _));
            }//release asquareds and bsquareds
            (Adjoint CrissCrossFp2ElementMontgomeryForm)(point::xs, point::zs);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Out-of-place doubling of an elliptic curve point in (X : Z) coordinates
    /// in a qubit register, on a curve given by $(A_{24}^+, C_{24})$ coordinates
    /// given in another qubit register. Requires clean ancillas which are 
    /// returned dirty.
    ///
    /// # Inputs
    /// ## point
    /// Qubit register encoding the (X : Z) coordinates to be doubled.
    /// ## curve
    /// Qubit register encoding the curve containing `point`, as 
    /// $(A_{24}^+,C_{24})$ coordinates.
    /// ## ancillas
    /// Clean ancillas which are returned dirty.
    /// ## blankOutput
    /// Qubit register assumed to be initialized to $\ket{0}$.
    /// This registers will be returned containing the doubled point.
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 3 from Appendix A.
    operation DoubleECPointMontgomeryXZOpen(
        point : ECPointMontgomeryXZ, 
        curve : ECCoordsMontgomeryFormAPlusC, 
        ancillas : Qubit[], 
        blankOutput : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            // Bookkeeping
            let nQubits = Length(point::xs::reals::register!);
            let modulus = point::xs::modulus;

            let (nSquAnc, nSquOut) = AncillaCountFp2SquMontgomeryForm(nQubits);
            let (nMulAnc, nMulOut) = AncillaCountFp2MulMontgomeryForm(nQubits);

            let internalAncillas = Partitioned(
                [nSquAnc, nSquAnc, nMulAnc,
                nMulAnc, nMulAnc, nMulAnc,
                nSquOut, nSquOut, nMulOut,
                nMulOut],
                ancillas
            );
            let squareAncillas = internalAncillas[0..1];
            let mulAncillas = internalAncillas[2..5];
            let aSquareds = QubitArrayAsFp2MontModInt(modulus, internalAncillas[6]);
            let bSquareds = QubitArrayAsFp2MontModInt(modulus, internalAncillas[7]);
            let cs = QubitArrayAsFp2MontModInt(modulus, internalAncillas[8]);
            let mulOutputs = [QubitArrayAsFp2MontModInt(modulus, internalAncillas[9])];

            // Let A:=x+z, B:=x-z
            CrissCrossFp2ElementMontgomeryForm(point::xs, point::zs);
            //Sets asquareds = A^2, bsquareds = B^2
            SquFp2ElementMontgomeryFormOpen(point::zs, squareAncillas[0], aSquareds);
            SquFp2ElementMontgomeryFormOpen(point::xs, squareAncillas[1], bSquareds);

            // Sets cs = C_24 * B^2
            MulFp2ElementMontgomeryFormOpen(curve::c24, bSquareds, mulAncillas[0], cs);

            // Sets the new x value = C_24 * A^2 * B^2
            MulFp2ElementMontgomeryFormOpen(aSquareds, cs, mulAncillas[1], blankOutput::xs);
            // asquareds = A^2 - B^2
            (Adjoint AddFp2ElementMontgomeryForm)(bSquareds, aSquareds);
            // cs = C_24 * B^2 + A_24^+ * (A^2 - B^2)
            MulFp2ElementMontgomeryFormOpen(curve::a24Plus, aSquareds, mulAncillas[2], mulOutputs[0]);
            AddFp2ElementMontgomeryForm(mulOutputs[0], cs);
            // Finishes doubled point
            MulFp2ElementMontgomeryFormOpen(aSquareds, cs, mulAncillas[3], blankOutput::zs);


            (Adjoint CrissCrossFp2ElementMontgomeryForm)(point::xs, point::zs);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open 
    /// doubling of a quantum
    /// elliptic curve point in Montgomery XZ form.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits necessary to encode the
    /// modulus p for the field $F_{p^2}$ of the curve.
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountDoubleECPoint (nQubits : Int) : (Int, Int) {
        let (nSquAncilla, nSquOutput) = AncillaCountFp2SquMontgomeryForm(nQubits);
        let (nMulAncilla, nMulOutput) = AncillaCountFp2MulMontgomeryForm(nQubits);
        let nSelfAncilla =  2 * nSquAncilla + 2 * nSquOutput
                + 4 * nMulAncilla + 2 * nMulOutput;
        let nSelfOutput = 2 * nMulOutput;
        return (nSelfAncilla, nSelfOutput);
    }

    /// # Summary
    /// Doubles a point repeatedly,
    /// keeping all ancilla and outputs from
    /// doing so.
    /// 
    /// # Input
    /// ## curve
    /// Qubit register with the curve of the
    /// point being doubled
    /// ## point
    /// Qubit register with the point to double.
    /// ## nDoublings
    /// The number of times to double the point
    /// ## ancillas
    /// Clean ancillas which are returned dirty.
    /// ## outputPoint
    /// Blank register to contain the final point
    operation IteratedPointDoublingOpen(
        curve : ECCoordsMontgomeryFormAPlusC,
        point : ECPointMontgomeryXZ,
        nDoublings : Int,
        ancillas : Qubit[],
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            let modulus = curve::a24Plus::modulus;
            let nQubits = Length(curve::a24Plus::reals::register!);
            let pointSize = 4 * nQubits;
            let (nDoubleAnc, nDoubleOut) = AncillaCountDoubleECPoint(nQubits);
            let internalAncillas = Partitioned([nDoublings * nDoubleAnc], ancillas);
            let doublingAncillas = EvenlyPartitionedArray(internalAncillas[0], nDoubleAnc);
            
            let points = [point] + QubitArrayAsECPointArray(nDoublings - 1, nQubits, modulus, internalAncillas[1]) + [outputPoint];

            for (idx in 0..nDoublings - 1){
                DoubleECPointMontgomeryXZOpen(points[idx], curve, doublingAncillas[idx], points[idx + 1]);
            }
        }
        adjoint controlled auto;
    }
    
    /// # Summary
    /// Returns the number of ancilla necessary for an
    // iterated open quantum point doubling 
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits necessary to encode the
    /// modulus p for the field $F_{p^2}$ of the curve.
    /// ## nDoublings
    /// The number of doublings to perform
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountIteratedPointDoubling (nQubits : Int, nDoublings : Int) : (Int, Int) {
        let (nDoubleAnc, nDoubleOut) = AncillaCountDoubleECPoint(nQubits);
        let nSelfAncilla =  nDoublings * nDoubleAnc + (nDoublings - 1) * nDoubleOut;
        let nSelfOutput = nDoubleOut;
        return (nSelfAncilla, nSelfOutput);
    }

    operation IteratedPointDouble(
        curve : ECCoordsMontgomeryFormAPlusC,
        point : ECPointMontgomeryXZ,
        nDoublings : Int,
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            IteratedPointDoubleLowMemory(curve, point, nDoublings, outputPoint);
            //IteratedPointDoubleHighMemory(curve, point, nDoublings, outputPoint);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Writes [2^n]P, for an elliptic curve
    /// point P and an integer n, to a blank
    /// qubit register.
    ///
    /// # Inputs
    /// ## curve
    /// Qubit register containing the curve
    /// containing P
    /// ## point
    /// The point P
    /// ## nDoublings
    /// The number of times to double P
    /// ## outputPoint
    /// The blank register to contain the output
    ///
    /// # Remarks
    /// This is a long sequence of identical out-of-place operations,
    /// so it needs some pebbling strategy. This operation uses the memory
    /// optimal strategy with a recursive binary tree (which then has depth
    /// $n^{log_2(3)}$).
    operation IteratedPointDoubleLowMemory(
        curve : ECCoordsMontgomeryFormAPlusC,
        point : ECPointMontgomeryXZ,
        nDoublings : Int,
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            (Controlled IteratedPointDoubleLowMemory)(new Qubit[0], (curve, point, nDoublings, outputPoint));
        }
        controlled(controls, ...){
            // Bookkeeping
            let modulus = curve::a24Plus::modulus;
            let nQubits = Length(curve::a24Plus::reals::register!);
            let pointSize = 4 * nQubits;
            using (outputs = Qubit[pointSize]){
                let midPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputs);
                if (nDoublings == 1){
                    let (nAncilla, _) = AncillaCountDoubleECPoint(nQubits);
                    using (ancillas = Qubit[nAncilla]){
                        DoubleECPointMontgomeryXZOpen(point, curve, ancillas, midPoint);
                        (Controlled CopyECPointMontgomeryXZ)(controls, (midPoint, outputPoint));
                        (Adjoint DoubleECPointMontgomeryXZOpen)(point, curve, ancillas, midPoint);
                    }
                } else {
                    let subRoundSize = nDoublings/2;
                    IteratedPointDoubleLowMemory(
                        curve,
                        point,
                        subRoundSize,
                        midPoint
                    );
                    (Controlled IteratedPointDoubleLowMemory)(controls,
                        (curve,
                        midPoint,
                        nDoublings - subRoundSize,
                        outputPoint)
                    );
                    (Adjoint IteratedPointDoubleLowMemory)(
                        curve,
                        point,
                        subRoundSize,
                        midPoint
                    );
                }
            }
        }
        controlled adjoint auto;
    }



    /// # Summary
    /// Writes [2^n]P, for an elliptic curve
    /// point P and an integer n, to a blank
    /// qubit register.
    ///
    /// # Inputs
    /// ## curve
    /// Qubit register containing the curve
    /// containing P
    /// ## point
    /// The point P
    /// ## nDoublings
    /// The number of times to double P
    /// ## outputPoint
    /// The blank register to contain the output
    ///
    /// # Remarks
    /// This is a long sequence of identical out-of-place operations,
    /// so it needs some pebbling strategy. This operation uses a 
    /// naive strategy of splitting n sequential steps into
    /// sqrt(n) "phases", each of which takes sqrt(n) out-of-place
    /// steps (hence requiring O(n * sqrt(n)) ancilla qubits), 
    /// copying out the result of the phase, then uncomputing the phase.
    operation IteratedPointDoubleHighMemory(
        curve : ECCoordsMontgomeryFormAPlusC,
        point : ECPointMontgomeryXZ,
        nDoublings : Int,
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            (Controlled IteratedPointDoubleHighMemory)(new Qubit[0], (curve, point, nDoublings, outputPoint));
        }
        controlled(controls, ...){
            // Bookkeeping
            let modulus = curve::a24Plus::modulus;
            let nQubits = Length(curve::a24Plus::reals::register!);
            let pointSize = 4 * nQubits;
            // We let the length of each unpebbled phase be the square root of the total number of rounds
            let subRoundSize = Max([Round(Sqrt(IntAsDouble(nDoublings)) - 0.5), 1]);
            // The last phase may have fewer iterations, which we test here
            let nRounds = (nDoublings % subRoundSize == 0) ? nDoublings / subRoundSize | nDoublings / subRoundSize + 1;
            let finalRoundSize = nDoublings - subRoundSize * (nRounds - 1); 
            
            // We need a temporary register to store the output of each doubling phase temporarily
            using (sparePointQubits = Qubit[pointSize]){
                let sparePoint =  QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, sparePointQubits);

                // Here we allocate the output registers for each round
                using (pebbledPointQubits = Qubit[pointSize * (nRounds - 1)]){
                    let pebbledPoints = [point] + QubitArrayAsECPointArray(nRounds - 1, nQubits, modulus, pebbledPointQubits);
                    for (idx in 0..nRounds - 2){
                        // Compute the point, copy out, then uncompute
                        let (nDoublingAnc, _) = AncillaCountIteratedPointDoubling(nQubits, subRoundSize);
                        using (doublingAncillas = Qubit[nDoublingAnc]){
                            IteratedPointDoublingOpen(
                                curve,
                                pebbledPoints[idx],
                                subRoundSize,
                                doublingAncillas,
                                sparePoint
                            );
                            CopyECPointMontgomeryXZ(sparePoint, pebbledPoints[idx + 1]);
                            (Adjoint IteratedPointDoublingOpen)(
                                curve,
                                pebbledPoints[idx],
                                subRoundSize,
                                doublingAncillas,
                                sparePoint
                            );
                        }
                    }
                    // Final round (may have a different size)
                    let (nFinalAnc, _) = AncillaCountIteratedPointDoubling(nQubits, finalRoundSize);
                    using (doublingAncillas = Qubit[nFinalAnc]){
                        IteratedPointDoublingOpen(
                            curve,
                            pebbledPoints[nRounds - 1],
                            finalRoundSize,
                            doublingAncillas,
                            sparePoint
                        );
                        // Copy to output (the only controlled step)
                        (Controlled CopyECPointMontgomeryXZ)(controls, (sparePoint, outputPoint));
                        (Adjoint IteratedPointDoublingOpen)(
                            curve,
                            pebbledPoints[nRounds - 1],
                            finalRoundSize,
                            doublingAncillas,
                            sparePoint
                        );
                    }
                    // Uncompute outputs from all previous phases
                    for (idx in nRounds - 2..(-1)..0){
                        let (nDoublingAnc, _) = AncillaCountIteratedPointDoubling(nQubits, subRoundSize);
                        using (doublingAncillas = Qubit[nDoublingAnc]){
                            IteratedPointDoublingOpen(
                                curve,
                                pebbledPoints[idx],
                                subRoundSize,
                                doublingAncillas,
                                sparePoint
                            );
                            (Adjoint CopyECPointMontgomeryXZ)(sparePoint, pebbledPoints[idx + 1]);
                            (Adjoint IteratedPointDoublingOpen)(
                                curve,
                                pebbledPoints[idx],
                                subRoundSize,
                                doublingAncillas,
                                sparePoint
                            );
                        }
                    }
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Writes [2^n]P, for an elliptic curve
    /// point P and an integer n, to a blank
    /// qubit register. Highest-memory strategy
    ///
    /// # Inputs
    /// ## curve
    /// Qubit register containing the curve
    /// containing P
    /// ## point
    /// The point P
    /// ## nDoublings
    /// The number of times to double P
    /// ## outputPoint
    /// The blank register to contain the output
    ///
    /// # Remarks
    /// This is a long sequence of identical out-of-place operations,
    /// so it needs some pebbling strategy. This version uses no pebbling:
    /// it simply allocates enough memory for all ancilla and all doublings,
    /// does them all, then uncomputes them all.
    operation IteratedPointDoubleFullMemory(
        curve : ECCoordsMontgomeryFormAPlusC,
        point : ECPointMontgomeryXZ,
        nDoublings : Int,
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            (Controlled IteratedPointDoubleFullMemory)(new Qubit[0], (curve, point, nDoublings, outputPoint));
        }
        controlled (controls, ...){
            let nQubits = Length(point::xs::reals::register!);
            let modulus = point::xs::modulus;
            let (nDoubleAncilla, nDoubleOut) = AncillaCountIteratedPointDoubling(nQubits, nDoublings);
            using ((doubledAncillas, doubledOutputs) = (Qubit[nDoubleAncilla], Qubit[nDoubleOut])){
                let tempDoubledPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, doubledOutputs);
                IteratedPointDoublingOpen(curve, point, nDoublings, doubledAncillas, tempDoubledPoint);
                CopyECPointMontgomeryXZ(tempDoubledPoint, outputPoint);
                (Adjoint IteratedPointDoublingOpen)(curve, point, nDoublings, doubledAncillas, tempDoubledPoint);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Given a classical point P and 
    /// qubit registers encoding points Q and Q-P,
    /// computes Q+P in a blank output qubit register. 
    /// Uses clean ancillas which are returned dirty.
    ///
    /// # Inputs
    // ## pointP
    /// Classical point P
    /// ## pointQ
    /// Qubit register encoding the point Q
    /// ## pointQminP
    /// Qubit register encoding the point Q - P
    /// ## ancillas
    /// Clean ancillas which are returned dirty
    /// ## outputPoint
    /// Qubit register assumed to be blank (all zeros)
    /// which will contain the output point
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 3 from Appendix A.
    ///
    /// # Remarks
    /// This operation has the same action as the function
    /// `DifferentialAddECPointMontgomeryXZClassical`, except
    /// when any of the inputs are (X:Z)=(0:0).
    operation DifferentialAddECPointMontgomeryXZOpen(
        pointP : ECPointMontgomeryXZClassical, 
        pointQ : ECPointMontgomeryXZ, 
        pointQminP : ECPointMontgomeryXZ, 
        ancillas : Qubit[],  
        outputPoint : ECPointMontgomeryXZ
    ): Unit {
        body (...){
            let nQubits = Length(pointQ::xs::reals::register!);
            let modulus = pointP::x::modulus;
            //Classical computations
            let pCrossPlus = AddFp2ElementClassical(pointP::x, pointP::z);
            let pCrossMinus = SubtractFp2ElementClassical(pointP::x, pointP::z);
            // Ancilla bookkeeping
            let (nInternalAncilla, _) = AncillaCountECPointDiffAddition(nQubits);
            AssertEnoughQubits(nInternalAncilla, "Differential point addition ancillas: ", ancillas);
            let (nSquAnc, nSquOut) = AncillaCountFp2SquMontgomeryForm(nQubits);
            let (nMulAnc, nMulOut) = AncillaCountFp2MulMontgomeryForm(nQubits);
            let (nMulConstAnc, nMulConstOut) = AncillaCountFp2MulConstantMontgomeryForm(nQubits);

            let internalAncillas = Partitioned(
                [nMulConstAnc, nMulConstAnc, nSquAnc, 
                    nSquAnc, nMulAnc, nMulAnc,
                    nMulConstOut, nMulConstOut,
                    nSquOut, nSquOut],
                ancillas
            );

            let constMulAncillas = internalAncillas[0..1];
            let squareAncillas = internalAncillas[2..3];
            let mulAncillas = internalAncillas[4..5];
            let constMulOutputs = [
                QubitArrayAsFp2MontModInt(modulus, internalAncillas[6]),
                QubitArrayAsFp2MontModInt(modulus, internalAncillas[7])
            ];
            let squareOutputs = [
                QubitArrayAsFp2MontModInt(modulus, internalAncillas[8]),
                QubitArrayAsFp2MontModInt(modulus, internalAncillas[9])
            ];
            // Sets Q_z = Q_x+Q_z, Q_x = Q_x-Q_z
            CrissCrossFp2ElementMontgomeryForm(pointQ::xs, pointQ::zs);
            // Sets C = (Q_x-Q_z)(P_x+P_z) and D = (Q_x+Q_z)(P_x-P_z)

            MulByConstantFp2MontgomeryFormOpen(pCrossMinus, pointQ::zs, constMulAncillas[1], constMulOutputs[1]);//D=t1
            MulByConstantFp2MontgomeryFormOpen(pCrossPlus, pointQ::xs, constMulAncillas[0], constMulOutputs[0]);// C=t0
            CrissCrossFp2ElementMontgomeryForm(constMulOutputs[0], constMulOutputs[1]);
            // C + D = xP+Q, C-D = ZP+Q
            SquFp2ElementMontgomeryFormOpen(constMulOutputs[1], squareAncillas[0], squareOutputs[0]);// (C+D)^2 = xPQ
            SquFp2ElementMontgomeryFormOpen(constMulOutputs[0], squareAncillas[1], squareOutputs[1]); // (C-D)^2 = zPQ
            //Finishes output
            MulFp2ElementMontgomeryFormOpen(pointQminP::zs, squareOutputs[0], mulAncillas[0], outputPoint::xs);
            MulFp2ElementMontgomeryFormOpen(pointQminP::xs, squareOutputs[1], mulAncillas[1], outputPoint::zs);
            //Correct input
            (Adjoint CrissCrossFp2ElementMontgomeryForm)(pointQ::xs, pointQ::zs);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open 
    /// differential addition of a classical and quantum
    /// elliptic curve point in Montgomery XZ form.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits necessary to encode the
    /// modulus p for the field $F_{p^2}$ of the curve.
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountECPointDiffAddition (nQubits : Int) : (Int, Int) {
        let (nMulConstAnc, nMulConstOut) = AncillaCountFp2MulMontgomeryForm(nQubits);
        let (nSquAncilla, nSquOutput) = AncillaCountFp2SquMontgomeryForm(nQubits);
        let (nMulAncilla, nMulOutput) = AncillaCountFp2MulMontgomeryForm(nQubits);
        let nSelfAncilla = 2 * nMulConstAnc + 2 * nMulConstOut 
                + 2 * nSquAncilla + 2 * nSquOutput
                + 2 * nMulAncilla;
        let nSelfOutput = 2 * nMulOutput;
        return (nSelfAncilla, nSelfOutput);
    }


    /// # Summary
    /// Uses a ladder of differential additions
    /// to compute Q + sP, where P is a classical 
    /// elliptic curve point, Q is a quantum elliptic
    /// curve point, and s is a quantum number, using
    /// an existing point Q - P as a helper.
    ///
    /// # Inputs
    /// ## pointPs
    /// Array containg P, 2P, 4P, up to 
    /// 2^nP, where n is the bit-length of the 
    /// coefficient s
    /// ## qPointQ
    /// Qubit register containing Q
    /// ## qPointQminP
    /// Qubit register containing Q - P
    /// ## coefficient
    /// Qubit register containing the coefficient s
    /// ## ancillas
    /// Clean ancilla which will be returned dirty.
    /// ## outputPoint
    /// Blank output register which will contain
    /// Q + sP
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 8 from Appendix A.
    operation MontgomeryXZPointLadderAllQuantumOpenWide(
        pointPs : ECPointMontgomeryXZClassical[], // array of P, 2P, 4P,...
        qPointQ : ECPointMontgomeryXZ,
        qPointQminP : ECPointMontgomeryXZ,
        coefficient : LittleEndian,
        ancillas : Qubit[],
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...) {
            let nRounds = Length(coefficient!);
            let nQubits = Length(outputPoint::xs::reals::register!);
            let modulus = qPointQ::xs::modulus;

            let (nDiffAddAnc, nDiffAddOut) = AncillaCountECPointDiffAddition(nQubits);
            let internalAncillas = Partitioned([nRounds * nDiffAddAnc], ancillas);
            // Creates an array of ancilla, one element for each differential addition
            let diffAddAncillas = EvenlyPartitionedArray(internalAncillas[0], nDiffAddAnc);

            // Creates an array of point registers for the qubit ladder, with the first equalling in the input, 
            // the last equalling the output
            let qPoints = [qPointQ] + QubitArrayAsECPointArray(nRounds - 1, nQubits, modulus, internalAncillas[1]) + [outputPoint];
            
            // See documentation for full explanation: There are two "modes" depending on whether
            // the bits of the coefficient are one or zero; we must swap Q and Q - P whenever
            // we switch modes.
            for (idx in 0.. nRounds - 1){
                // Needed for the first swap if we are in the "zero mode""
                if (idx == 0){
                    X(coefficient![0]);
                }
                // Swap "modes" if necessary
                (Controlled SwapFp2ElementMontgomeryForm)([coefficient![idx]], (qPointQminP::xs, qPoints[idx]::xs));
                (Controlled SwapFp2ElementMontgomeryForm)([coefficient![idx]], (qPointQminP::zs, qPoints[idx]::zs));
                // uncompute
                if (idx == 0){
                    X(coefficient![0]);
                }
                // Perform addition
                DifferentialAddECPointMontgomeryXZOpen(pointPs[idx], qPoints[idx], qPointQminP, diffAddAncillas[idx], qPoints[idx+1]);
                // Fix bit for that round, check if the mode changes for the next round
                if (idx > 0){
                    (Adjoint CNOT)(coefficient![idx - 1], coefficient![idx]);
                }
                if (idx < nRounds - 1){
                    CNOT(coefficient![idx], coefficient![idx + 1]);
                }
            }
            // final conditional swap:
            X(coefficient![nRounds - 1]);
            (Controlled SwapFp2ElementMontgomeryForm)([coefficient![nRounds - 1]], (qPointQminP::xs, qPoints[nRounds]::xs));
            (Controlled SwapFp2ElementMontgomeryForm)([coefficient![nRounds - 1]], (qPointQminP::zs, qPoints[nRounds]::zs));
            X(coefficient![nRounds - 1]);
            
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open 
    /// quantum point ladder
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits necessary to encode the
    /// modulus p for the field $F_{p^2}$ of the curve.
    /// ## nRounds
    /// The number of rounds in the ladder (the bit
    /// length of the coefficient)
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountPointLadder (nQubits : Int, nRounds : Int) : (Int, Int) {
        let (nDiffAddAnc, nDiffAddOut) = AncillaCountECPointDiffAddition(nQubits);
        let nSelfAncilla =  nRounds * nDiffAddAnc + (nRounds - 1) * nDiffAddOut;
        let nSelfOutput = nDiffAddOut;
        return (nSelfAncilla, nSelfOutput);
    }

    /// # Summary
    /// Computes Q + sP for classical
    /// elliptic curve points P and Q
    /// and quantum coefficient s.
    ///
    /// # Inputs
    /// ## curve
    /// The curve containing P and Q
    /// ## pointP
    /// The point P
    /// ## pointQ
    /// The point Q
    /// ## pointQminP
    /// The point Q - P
    /// ## coefficient
    /// The qubit register containing s
    /// ## outputPoint
    /// Blank qubit register which will contain
    /// Q + sP
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 8 from Appendix A.f
    operation MontgomeryXZPointLadder(
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointQminP : ECPointMontgomeryXZClassical,
        coefficient : LittleEndian,
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            MontgomeryXZPointLadderLowMemory(curve, pointP, pointQ, pointQminP, coefficient, outputPoint);
            //MontgomeryXZPointLadderHighMemory(curve, pointP, pointQ, pointQminP, coefficient, outputPoint);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes Q + sP for classical
    /// elliptic curve points P and Q
    /// and quantum coefficient s.
    ///
    /// # Inputs
    /// ## curve
    /// The curve containing P and Q
    /// ## pointP
    /// The point P
    /// ## pointQ
    /// The point Q
    /// ## pointQminP
    /// The point Q - P
    /// ## coefficient
    /// The qubit register containing s
    /// ## outputPoint
    /// Blank qubit register which will contain
    /// Q + sP
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 8 from Appendix A.
    ///
    /// # Remarks
    /// This is a long sequence of identical out-of-place operations,
    /// so it needs some pebbling strategy. This operation uses a
    /// low-memory strategy with a binary tree of recursive calls.
    /// Because the "inner" operation outputs both Q + sP
    /// and Q + sP - 2^nP, this needs to uncompute that. This can
    /// likely be optimized in future versions.
    operation MontgomeryXZPointLadderLowMemory(
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointQminP : ECPointMontgomeryXZClassical,
        coefficient : LittleEndian,
        output : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            let modulus = curve::a24Plus::modulus;
            let nRounds = Length(coefficient!);
            let nQubits = Length(output::xs::reals::register!);
            let pointSize = 4 * nQubits;
            using ((qQubits, qMinPQubits, outputQQubits, outputQminPQubits) = (Qubit[pointSize], Qubit[pointSize], Qubit[pointSize], Qubit[pointSize])){
                let qPointQ = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, qQubits);
                let qPointQminP = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, qMinPQubits);
                // outputQminP is pointless actually: these are blank qubits that remain unchanged
                // But it's simpler than trying to construct a point tuple that references an empty array
                let outputQminP = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQminPQubits);
                let outputQ = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQQubits);
                EncodeECPointMontgomeryXZ(pointQ, qPointQ);
                EncodeECPointMontgomeryXZ(pointQminP,qPointQminP);
                let pointPs = DoubledPointArray(pointP, curve, nRounds);
                MontgomeryXZPointLadderLowMemoryInner(
                    curve,
                    pointPs,
                    qPointQ ,
                    qPointQminP,
                    coefficient,
                    output,
                    outputQminP,
                    true
                );
                (Adjoint EncodeECPointMontgomeryXZ)(pointQ, qPointQ);
                (Adjoint EncodeECPointMontgomeryXZ)(pointQminP,qPointQminP);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes Q + sP for classical 
    /// elliptic curve point P, quantum point Q
    /// and quantum coefficient s.
    ///
    /// # Inputs
    /// ## curve
    /// The curve containing P and Q
    /// ## pointPs
    /// An array of P, 2P, 4P, ...
    /// ## pointQ
    /// The point Q
    /// ## pointQminP
    /// The point Q - P
    /// ## coefficient
    /// The qubit register containing s
    /// ## outputQ
    /// Blank qubit register which will contain
    /// Q + sP
    /// ## outputQminP
    /// Blank qubit register which will contain
    /// Q + sP - 2^nP, where n is the big length of
    /// the coefficient s
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 8 from Appendix A.
    operation MontgomeryXZPointLadderLowMemoryInner(
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointPs : ECPointMontgomeryXZClassical[],
        pointQ : ECPointMontgomeryXZ,
        pointQminP : ECPointMontgomeryXZ,
        coefficient : LittleEndian,
        outputQ : ECPointMontgomeryXZ,
        outputQminP : ECPointMontgomeryXZ,
        isFinal : Bool
    ) : Unit {
        body (...){
            (Controlled MontgomeryXZPointLadderLowMemoryInner)(new Qubit[0], (curve, pointPs, pointQ, pointQminP, coefficient, outputQ, outputQminP, isFinal));
        }
        controlled (controls, ...){
            // Bookkeeping
            let modulus = curve::a24Plus::modulus;
            let nRounds = Length(coefficient!);
            

            let nQubits = Length(outputQ::xs::reals::register!);
            let pointSize = 4 * nQubits;
            // The "spare point" is what each open point ladder uses for its final output
            // It gets copied out to a larger array each time
            using ((midQQubits, midQminPQubits) = (Qubit[pointSize], Qubit[pointSize])){
                let midQ = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, midQQubits);
                let midQminP = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, midQminPQubits);
                if (nRounds == 0) {
                    (Controlled CopyECPointMontgomeryXZ)(controls, (pointQ, outputQ));
                    (Controlled CopyECPointMontgomeryXZ)(controls, (pointQminP, outputQminP));
                } elif (nRounds == 1){
                    let (nAncillas, _) = AncillaCountECPointDiffAddition(nQubits);
                    using (ancillas = Qubit[nAncillas]){
                        X(coefficient![0]);
                        (Controlled SwapECPointMontgomeryXZ)([coefficient![0]], (pointQ, pointQminP));
                        DifferentialAddECPointMontgomeryXZOpen(pointPs[0], pointQ, pointQminP, ancillas, midQ);
                        //copy out what's needed
                        (Controlled SwapECPointMontgomeryXZ)([coefficient![0]], (midQ, pointQminP));
                        (Controlled CopyECPointMontgomeryXZ)(controls, (midQ, outputQ));
                        if (not isFinal){
                            // We don't want to copy out QminP if it's the last one
                            (Controlled CopyECPointMontgomeryXZ)(controls, (pointQminP, outputQminP));
                        }
                        (Controlled SwapECPointMontgomeryXZ)([coefficient![0]], (midQ, pointQminP));
                        (Adjoint DifferentialAddECPointMontgomeryXZOpen)(pointPs[0], pointQ, pointQminP, ancillas, midQ);
                        (Controlled SwapECPointMontgomeryXZ)([coefficient![0]], (pointQ, pointQminP));
                        X(coefficient![0]);
                    }
                } else { 
                    let subRoundSize = nRounds/2;
                    MontgomeryXZPointLadderLowMemoryInner(
                        curve,
                        pointPs[0.. subRoundSize - 1],
                        pointQ,
                        pointQminP,
                        LittleEndian(coefficient![0.. subRoundSize - 1]),
                        midQ,
                        midQminP,
                        false
                    );
                    (Controlled MontgomeryXZPointLadderLowMemoryInner)(controls,
                        (curve,
                        pointPs[subRoundSize.. nRounds - 1],
                        midQ,
                        midQminP,
                        LittleEndian(coefficient![subRoundSize .. nRounds - 1]),
                        outputQ,
                        outputQminP,
                        isFinal)
                    );
                    (Adjoint MontgomeryXZPointLadderLowMemoryInner)(
                        curve,
                        pointPs[0.. subRoundSize - 1],
                        pointQ,
                        pointQminP,
                        LittleEndian(coefficient![0.. subRoundSize - 1]),
                        midQ,
                        midQminP,
                        false
                    );
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes Q + sP for classical
    /// elliptic curve points P and Q
    /// and quantum coefficient s.
    ///
    /// # Inputs
    /// ## curve
    /// The curve containing P and Q
    /// ## pointP
    /// The point P
    /// ## pointQ
    /// The point Q
    /// ## pointQminP
    /// The point Q - P
    /// ## coefficient
    /// The qubit register containing s
    /// ## outputPoint
    /// Blank qubit register which will contain
    /// Q + sP
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 8 from Appendix A.
    ///
    /// # Remarks
    /// This is a long sequence of identical out-of-place operations,
    /// so it needs some pebbling strategy. This operation uses a 
    /// naive strategy of splitting n sequential steps into
    /// sqrt(n) "phases", each of which takes sqrt(n) out-of-place
    /// steps (hence requiring O(n * sqrt(n)) ancilla qubits), 
    /// copying out the result of the phase, then uncomputing the phase.
    operation MontgomeryXZPointLadderHighMemory(
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointQminP : ECPointMontgomeryXZClassical,
        coefficient : LittleEndian,
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            (Controlled MontgomeryXZPointLadderHighMemory)(new Qubit[0], (curve, pointP, pointQ, pointQminP, coefficient, outputPoint));
        }
        controlled (controls, ...){
            // Bookkeeping
            let modulus = curve::a24Plus::modulus;
            let nRounds = Length(coefficient!);
            // We let each unpebbled round be the square root of the total number of rounds
            let subRoundSize = Round(Sqrt(IntAsDouble(nRounds)) - 0.5);
            let doubledPs = DoubledPointArray(pointP, curve, nRounds);
            // Partition the array of coefficients and power-multiplies of P
            let subRounds = Partitioned(ConstantArray(subRoundSize, subRoundSize), coefficient!);
            let subDoubledPs = Partitioned(ConstantArray(subRoundSize, subRoundSize), doubledPs);
            // The Partitioned function will give an empty array as the final entry if
            // the input partition perfectly covers the array. This empty array would cause errors,
            // so we need to set nPebbles to be the length of the non-empty part of `subRounds`
            let nSubRounds = Length(subRounds);
            let nPebbles = Length(subRounds[nSubRounds - 1]) == 0 ? nSubRounds  - 1 | nSubRounds;
            let nQubits = Length(outputPoint::xs::reals::register!);
            let pointSize = 4 * nQubits;
            // The "spare point" is what each open point ladder uses for its final output
            // It gets copied out to a larger array each time
            using (sparePointQQubits = Qubit[pointSize]){
                let sparePointQ = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, sparePointQQubits);
                // Here we allocate all the qubits we will use for pebbling. 
                // These are the intermediate points, representing the output of each unpebbled phase
                using ((pebblePointQQubits, pebblePointQminPQubits) = (Qubit[pointSize * nPebbles], Qubit[pointSize * nPebbles])){
                    let pebbledQPoints = QubitArrayAsECPointArray(nPebbles, nQubits, modulus, pebblePointQQubits) + [outputPoint];
                    let pebbledQminPPoints = QubitArrayAsECPointArray(nPebbles, nQubits, modulus, pebblePointQminPQubits);
                    // The first point in the array should be the input points
                    EncodeECPointMontgomeryXZ(pointQ, pebbledQPoints[0]);
                    EncodeECPointMontgomeryXZ(pointQminP, pebbledQminPPoints[0]);
                    for (idx in 0..nPebbles - 1) {
                        // For each unpebbled phase, we allocate all the necessary ancilla
                        let (nLadderAnc, _) = AncillaCountPointLadder (nQubits, Length(subRounds[idx]));
                        using (ladderAncillas = Qubit[nLadderAnc]){
                            // Compute that phase, copy out the answer, and uncompute
                            MontgomeryXZPointLadderAllQuantumOpenWide(
                                subDoubledPs[idx],
                                pebbledQPoints[idx],
                                pebbledQminPPoints[idx],
                                LittleEndian(subRounds[idx]),
                                ladderAncillas,
                                sparePointQ
                            );
                            if (idx == nPebbles - 1){
                                // For the last phase, we don't need Q - P, and we also should control it
                                (Controlled CopyECPointMontgomeryXZ)(controls, (sparePointQ, pebbledQPoints[idx + 1]));
                            } else {
                                CopyECPointMontgomeryXZ(pebbledQminPPoints[idx], pebbledQminPPoints[idx + 1]);
                                CopyECPointMontgomeryXZ(sparePointQ, pebbledQPoints[idx + 1]);
                            }
                            (Adjoint MontgomeryXZPointLadderAllQuantumOpenWide)(
                                subDoubledPs[idx],
                                pebbledQPoints[idx],
                                pebbledQminPPoints[idx],
                                LittleEndian(subRounds[idx]),
                                ladderAncillas,
                                sparePointQ
                            );
                        }	
                    }
                    // Now we must uncompute the outputs of all the phases
                    for (idx in (nPebbles - 2)..(-1)..0) {
                        let (nLadderAnc, nLadderOut) = AncillaCountPointLadder (nQubits, Length(subRounds[idx]));
                        using (ladderAncillas = Qubit[nLadderAnc]){
                            MontgomeryXZPointLadderAllQuantumOpenWide(
                                subDoubledPs[idx],
                                pebbledQPoints[idx],
                                pebbledQminPPoints[idx],
                                LittleEndian(subRounds[idx]),
                                ladderAncillas,
                                sparePointQ
                            );
                            if (idx == nPebbles - 1){
                                (Adjoint Controlled CopyECPointMontgomeryXZ)(controls, (pebbledQminPPoints[idx], pebbledQminPPoints[idx + 1]));
                                (Adjoint Controlled CopyECPointMontgomeryXZ)(controls, (sparePointQ, pebbledQPoints[idx + 1]));
                            } else {
                                (Adjoint CopyECPointMontgomeryXZ)(pebbledQminPPoints[idx], pebbledQminPPoints[idx + 1]);
                                (Adjoint CopyECPointMontgomeryXZ)(sparePointQ, pebbledQPoints[idx + 1]);
                            }
                            (Adjoint MontgomeryXZPointLadderAllQuantumOpenWide)(
                                subDoubledPs[idx],
                                pebbledQPoints[idx],
                                pebbledQminPPoints[idx],
                                LittleEndian(subRounds[idx]),
                                ladderAncillas,
                                sparePointQ
                            );
                        }	
                    }
                    // Uncompute the input points
                    (Adjoint EncodeECPointMontgomeryXZ)(pointQ, pebbledQPoints[0]);
                    (Adjoint EncodeECPointMontgomeryXZ)(pointQminP, pebbledQminPPoints[0]);
                }
            }
            
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes the j-invariant of a quantum elliptic curve E,
    /// given in $(A_{24}^+,C_{24})$ coordinates. Uses clean 
    /// ancilla which are returned dirty.
    ///
    /// # Inputs
    /// ## curve
    /// The curve E 
    /// ## ancillas
    /// Clean ancillas which are returned dirty.
    /// ## blankOutput
    /// Empty qubit register which will be returned containing j(E)
    operation GetJInvariantAPlusCOpen (curve : ECCoordsMontgomeryFormAPlusC, ancillas : Qubit[], blankOutput : Fp2MontModInt) : Unit {
        /// Main idea: We convert the curve to (A : C) form, then call GetJInvariantACOpen
        /// The conversion is non-adjointable, so we must specify the adjoint manually.
        body (...){
            (Controlled GetJInvariantAPlusCOpen)(new Qubit[0], (curve, ancillas, blankOutput));
        }
        controlled  (controls, ...){
            let curveAC = ECCoordsAPlusCToAC(curve); //convert curve to the right form
            (Controlled GetJInvariantACOpen)(controls, (curveAC, ancillas, blankOutput));
            let originalCurve = ECCoordsACToAPlusC(curveAC); //converts back (acts as the adjoint)
        }
        adjoint (...){
            (Controlled Adjoint GetJInvariantAPlusCOpen)(new Qubit[0], (curve, ancillas, blankOutput));
        }
        controlled adjoint (controls, ...){
            let curveAC = ECCoordsAPlusCToAC(curve); //convert curve to the right form
            (Adjoint Controlled GetJInvariantACOpen)(controls, (curveAC, ancillas, blankOutput));
            let originalCurve = ECCoordsACToAPlusC(curveAC); //converts back (acts as the adjoint)
        }
    }

    /// # Summary
    /// Returns the number of ancilla necessary for an open 
    /// j invariant computation from $(A_{24}^+,C{24})$ 
    /// coordinates.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits necessary to encode the
    /// modulus p for the field $F_{p^2}$ of the curve.
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountJInvariantAPlusC(nQubits : Int) : (Int, Int) {
        return AncillaCountJInvariantAC(nQubits);
    }

    /// # Summary
    /// Computes the j-invariant of a quantum elliptic curve E,
    /// given in $(A_{24}^+,C_{24})$ coordinates.
    ///
    /// # Inputs
    /// ## curve
    /// Qubit register containing the coordinates
    /// ## jInvariant
    /// Blank qubit register to contain the j-invariant.
    operation GetJInvariantAPlusC (curve : ECCoordsMontgomeryFormAPlusC, jInvariant : Fp2MontModInt) : Unit {
        body (...){
            (Controlled GetJInvariantAPlusC)(new Qubit[0], (curve, jInvariant));
        }
        controlled (controls, ...){
            let nQubits = Length(curve::a24Plus::reals::register!);
            let modulus = curve::a24Plus::modulus;
            let (nAncilla, nOutputs) = AncillaCountJInvariantAPlusC(nQubits);
            using ((ancillas, outputs) = (Qubit[nAncilla], Qubit[nOutputs])){
                let internalJInvariant = QubitArrayAsFp2MontModInt(modulus, outputs);
                GetJInvariantAPlusCOpen(curve, ancillas, internalJInvariant);
                (Controlled CopyFp2MontModInt)(controls, (internalJInvariant, jInvariant));
                (Adjoint GetJInvariantAPlusCOpen)(curve, ancillas, internalJInvariant);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes the j-invariant of a quantum elliptic curve E,
    /// given in projective (A : C) coordinates. Uses clean 
    /// ancilla which are returned dirty.
    ///
    /// # Inputs
    /// ## curve
    /// The curve E 
    /// ## ancillas
    /// Clean ancillas which are returned dirty.
    /// ## blankOutput
    /// Empty qubit register which will be returned containing j(E)
    operation GetJInvariantACOpen (curve : ECCoordsMontgomeryFormAC, ancillas : Qubit[], blankOutput : Fp2MontModInt) : Unit {
        body (...){
            let nQubits = Length(curve::aCoeff::reals::register!);
            let modulus = curve::aCoeff::modulus;
            let tempAncillas = ancillas;
            let (nSquAnc, nSquOut) = AncillaCountFp2SquMontgomeryForm(nQubits);
            let (nMulAnc, nMulOut) = AncillaCountFp2MulMontgomeryForm(nQubits);
            let (nInvAnc, nInvOut) = AncillaCountFp2InvMontgomeryForm(nQubits);
            let internalAncillas = Partitioned(
                [nSquAnc, nSquAnc, nSquAnc, nSquAnc, //0-3
                nMulAnc, nMulAnc, nMulAnc, nInvAnc, // 4-7
                nSquOut, nSquOut, nSquOut, nMulOut, //8-11
                nSquOut, nMulOut, nInvOut], //12-14
                ancillas
            );
            let squareAncillas = internalAncillas[0..3];
            let mulAncillas = internalAncillas[4..6];
            let invAncillas = [internalAncillas[7]];
            let aSquared = QubitArrayAsFp2MontModInt(modulus, internalAncillas[8]);
            let cSquared = QubitArrayAsFp2MontModInt(modulus, internalAncillas[9]);
            let cFourthed = QubitArrayAsFp2MontModInt(modulus, internalAncillas[10]);
            let denominator = QubitArrayAsFp2MontModInt(modulus, internalAncillas[11]);
            let squOutput = QubitArrayAsFp2MontModInt(modulus, internalAncillas[12]);
            let numerator = QubitArrayAsFp2MontModInt(modulus, internalAncillas[13]);
            let denomInverse = QubitArrayAsFp2MontModInt(modulus, internalAncillas[14]);

            SquFp2ElementMontgomeryFormOpen(curve::aCoeff, squareAncillas[0], aSquared);// aSquared = A^2
            SquFp2ElementMontgomeryFormOpen(curve::cCoeff, squareAncillas[1], cSquared); // cSquared = C^2
            SquFp2ElementMontgomeryFormOpen(cSquared, squareAncillas[2], cFourthed); // cFourthed = C^4
            DblFp2MontgomeryForm(cSquared); // cSquared = 2C^2
            DblFp2MontgomeryForm(cSquared); // cSquared = 4C^2
            (Adjoint AddFp2ElementMontgomeryForm)(cSquared, aSquared); // aSquared = A^2 - 4C^2
            MulFp2ElementMontgomeryFormOpen(cFourthed, aSquared, mulAncillas[0], denominator); // denominator = C^4(A^2-C^4)
            DblFp2MontgomeryForm(aSquared); // aSquared = 2A^2 - 8C^2)
            DblFp2MontgomeryForm(aSquared); // aSquared = 4A^2 - 16C^2)
            AddFp2ElementMontgomeryForm(cSquared, aSquared); //aSquared = 4A^2 - 12C^2 = 4(A^2 - 3C^2)
            SquFp2ElementMontgomeryFormOpen(aSquared, squareAncillas[3], squOutput); // squOutput = 16(A^2 - 3C^2)^2
            MulFp2ElementMontgomeryFormOpen(aSquared, squOutput, mulAncillas[1], numerator); // numerator = 64(A^2 - 3C^2)^2
            DblFp2MontgomeryForm(numerator); // numerator = 128(A^2 - 3C^2)^2
            DblFp2MontgomeryForm(numerator); //numerator = 256(A^2 - 3C^2)^2
            InvFp2ElementMontgomeryFormOpen(denominator, invAncillas[0], denomInverse); // denomInv = 1/(C^4(A^2 - C^4))
            MulFp2ElementMontgomeryFormOpen(denomInverse, numerator, mulAncillas[2], blankOutput); // blankOutput = j-invariant
        }
        controlled adjoint auto;
    }
    
    /// # Summary
    /// Returns the number of ancilla necessary for an open 
    /// j invariant computation from projective (A : C)
    /// coordinates.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits necessary to encode the
    /// modulus p for the field $F_{p^2}$ of the curve.
    ///
    /// # Outputs
    /// ## (Int, Int)
    /// The number of ancilla necessary in the first argument,
    /// and the number of output qubits in the second argument.
    function AncillaCountJInvariantAC(nQubits : Int) : (Int, Int) {
        let (nSquAnc, nSquOut) = AncillaCountFp2SquMontgomeryForm(nQubits);
        let (nMulAnc, nMulOut) = AncillaCountFp2MulMontgomeryForm(nQubits);
        let (nInvAnc, nInvOut) = AncillaCountFp2InvMontgomeryForm(nQubits);
        let nSelfAncilla = 4 * nSquAnc + 3 * nMulAnc + nInvAnc 
            + 4 * nSquOut * 2 * nMulOut + nInvOut;
        let nSelfOut = nMulOut;
        return (nSelfAncilla, nSelfOut);
    }

    /// # Summary
    /// From a point P of exact order 2 and another point Q
    /// not in <P>, computes f(Q) for the isogeny f with kernel
    /// equal to <P>. Requires P = (X : Z) to be given as
    /// (X - Z, X + Z)
    ///
    /// # Inputs
    /// ## kernelPoint
    /// The point P of exact order 2.
    /// ## targetPoint
    /// The point Q as input to the isogeny.
    /// ## outputPoint
    /// Blank qubit register to store f(Q)
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 12 from Appendix A.
    ///
    /// # Remarks
    /// The first step of Algorithm 12 is to compute X - Z and X + Z for the 
    /// kernel point. When performing multiple parallel isogenies with the same
    /// kernel point, it saves computation to keep the kernel point in this form.
    operation _TwoIsogenyOfCrossedKernelPoint(
        kernelPoint : ECPointMontgomeryXZ, 
        targetPoint : ECPointMontgomeryXZ, 
        outputPoint : ECPointMontgomeryXZ
    ) : Unit {
        body (...){
            (Controlled _TwoIsogenyOfCrossedKernelPoint)(new Qubit[0], (kernelPoint, targetPoint, outputPoint));
        }
        controlled (controls, ...){
            let nQubits = Length(kernelPoint::xs::reals::register!);
            let modulus = kernelPoint::xs::modulus;
            CrissCrossFp2ElementMontgomeryForm(targetPoint::xs, targetPoint:: zs); // xs = x - z, zs = x + z
            using ((crossPlusQubits, crossMinusQubits) = (Qubit[2 * nQubits], Qubit[2 * nQubits])){
                let crossPlus = QubitArrayAsFp2MontModInt(modulus, crossPlusQubits); 
                let crossMinus = QubitArrayAsFp2MontModInt(modulus, crossMinusQubits);
                MulAndXorFp2ElementMontgomeryForm(kernelPoint::xs, targetPoint::zs, crossMinus); //crossMinus = (Px-Pz)(Qx+Qz)
                MulAndXorFp2ElementMontgomeryForm(kernelPoint::zs, targetPoint::xs, crossPlus); //crossPlus = (Px+Pz)(Qx-Qz)
                CrissCrossFp2ElementMontgomeryForm(crossPlus, crossMinus); // crossPlus = (Px+Pz)(Qx-Qz) - (Px-Pz)(Qx+Qz) 
                                                                            // crossMinus =(Px+Pz)(Qx-Qz) + (Px-Pz)(Qx+Qz)
                (Adjoint CrissCrossFp2ElementMontgomeryForm)(targetPoint::xs, targetPoint::zs); // xs = x; zs = z
                // Final result
                (Controlled MulAndXorFp2ElementMontgomeryForm)(controls, (crossPlus, targetPoint::zs, outputPoint::zs));
                (Controlled MulAndXorFp2ElementMontgomeryForm)(controls, (crossMinus, targetPoint::xs, outputPoint::xs));
                //uncompute
                CrissCrossFp2ElementMontgomeryForm(targetPoint::xs, targetPoint::zs);
                (Adjoint CrissCrossFp2ElementMontgomeryForm)(crossPlus, crossMinus); 
                (Adjoint MulAndXorFp2ElementMontgomeryForm)(kernelPoint::xs, targetPoint::zs, crossMinus);
                (Adjoint MulAndXorFp2ElementMontgomeryForm)(kernelPoint::zs, targetPoint::xs, crossPlus);
            }
            // These are actually unnecessary within the SIKE protocol
            (Adjoint CrissCrossFp2ElementMontgomeryForm)(targetPoint::xs, targetPoint:: zs);
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// From a point P of exact order 2 and another point Q
    /// not in <P>, computes f(Q) for the isogeny f with kernel
    /// equal to <P>. 
    ///
    /// # Inputs
    /// ## kernelPoint
    /// The point P of exact order 2.
    /// ## targetPoint
    /// The point Q as input to the isogeny.
    /// ## outputPoint
    /// Blank qubit register to store f(Q)
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 12 from Appendix A.
    operation TwoIsogenyOfPoint(kernelPoint : ECPointMontgomeryXZ, targetPoint : ECPointMontgomeryXZ, outputPoint : ECPointMontgomeryXZ) : Unit {
        body (...){
            (Controlled TwoIsogenyOfPoint)(new Qubit[0], (kernelPoint, targetPoint, outputPoint));
        }
        controlled (controls, ...){
            let nQubits = Length(kernelPoint::xs::reals::register!);
            let modulus = kernelPoint::xs::modulus;
            CrissCrossFp2ElementMontgomeryForm(kernelPoint::xs, kernelPoint::zs); // xs = x- z, zs = x + z
            (Controlled _TwoIsogenyOfCrossedKernelPoint)(controls, (kernelPoint, targetPoint, outputPoint));
            (Adjoint CrissCrossFp2ElementMontgomeryForm)(kernelPoint::xs, kernelPoint::zs); 
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Given a point P of exact order 2 in a qubit register, implicitly
    /// on an elliptic curve E, computes the curve isogenous
    /// to E via the isogeny with kernel <P>
    ///
    /// # Inputs
    /// ## point
    /// The point P
    /// ## outputCurve
    /// Blank qubit register to contain the output
    ///
    /// # References
    /// David Jao et al., Supersingular Isogeny Key Encapsulation specification.
    ///    https : //sike.org/files/SIDH-spec.pdf
    ///    Follows Algorithm 11 from Appendix A.
    ///	   The subtraction in step 3 is reversed.
    operation TwoIsogenyOfCurveMontgomeryXZ(point : ECPointMontgomeryXZ, outputCurve : ECCoordsMontgomeryFormAPlusC): Unit{
        body (...){
            (Controlled TwoIsogenyOfCurveMontgomeryXZ)(new Qubit[0], (point, outputCurve));
        }
        controlled (controls, ...){
            let nQubits = Length(point::xs::reals::register!);
            let modulus = point::xs::modulus;
            (Controlled Adjoint SquAndAddFp2ElementMontgomeryForm)(controls, (point::xs, outputCurve::a24Plus)); //a24Plus = - x^2
            (Controlled SquAndXorFp2ElementMontgomeryForm)(controls, (point::zs, outputCurve::c24)); // c24 = z^2
            (Controlled AddFp2ElementMontgomeryForm)(controls, (outputCurve::c24, outputCurve::a24Plus)); // a24Plus = z^2 - x^2
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Recursively computes a power-of-two isogeny
    /// whose kernel is generated by point given as 
    /// input in a quantum register. 
    /// 
    /// # Inputs
    /// ## startingPoint
    /// The generator of the kernel of the isogeny
    /// ## startingCurve 
    /// The curve which contains the starting point
    /// ## height
    /// The power of two that is the degree of the
    /// isogeny (equivalently, the log in base 2
    /// of the order of the starting point).
    /// ## trailingPoints
    /// An array (possibly empty) of points
    /// also on the curve, which the operation
    /// will map through the isogeny it computes.
    /// ## outputTrailingPoints
    /// The register where the operation will save the output
    /// of each trailingPoint after mapping it through the
    /// isogeny
    /// ## outputCurve
    /// The codomain of the isogeny calculated.
    /// ## copyOp
    /// When the operation finishes, it will call this 
    /// operation on the final outputCurve before 
    /// being uncomputed. 
    ///
    /// # Remarks
    /// This uses a naive recursive strategy of 
    /// using a left tree of size 1/3 of the total height,
    /// and a right tree of 2/3 of the total height.
    operation IsogenyTreeMiddle(
        startingPoint : ECPointMontgomeryXZ,
        startingCurve : ECCoordsMontgomeryFormAPlusC,
        height : Int,
        trailingPoints : ECPointMontgomeryXZ[],
        outputTrailingPoints : ECPointMontgomeryXZ[],
        outputCurve : ECCoordsMontgomeryFormAPlusC,
        copyOp : (ECCoordsMontgomeryFormAPlusC => Unit is Ctl + Adj)
    ) : Unit {
        body (...){
            let nQubits = Length(startingPoint::xs::reals::register!);
            let modulus = startingPoint::xs::modulus;
            let nTrailingPoints = Length(trailingPoints);
            // Here we do a naive pebbling: take 2/3 each time
            if (height <= 1){//base case; the cut-off is somewhat arbitrary
                IsogenyTreeSmall(
                    startingPoint,
                    startingCurve,
                    height,
                    trailingPoints,
                    outputTrailingPoints,
                    outputCurve,
                    copyOp
                );
            } else {
                let (leftHeight, rightHeight) = OptimalSIKEDivision(height, nTrailingPoints, nQubits, false) ;
                using (leftPointQubits = Qubit[4 * nQubits]){
                    let leftPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, leftPointQubits);
                    
                    // Double input point to get start of left recursion
                    IteratedPointDouble(startingCurve, startingPoint, rightHeight, leftPoint);
                    // Now we need trailing points for the next recursive call
                    
                    using ((trailingPointQubits, midCurveQubits, rightPointQubits) = (Qubit[nTrailingPoints * 4 * nQubits], Qubit[4 * nQubits], Qubit[4 * nQubits])){
                        let midTrailingPoints = QubitArrayAsECPointArray(nTrailingPoints, nQubits, modulus, trailingPointQubits);
                        let midCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, midCurveQubits);
                        let rightPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, rightPointQubits);
                        // compute left side
                        IsogenyTreeMiddle(
                            leftPoint,
                            startingCurve,
                            leftHeight,
                            [startingPoint] + trailingPoints,
                            [rightPoint] + midTrailingPoints,
                            midCurve,
                            NoOp<ECCoordsMontgomeryFormAPlusC>//will never copy from left tree
                        );
                        // compute right side
                        IsogenyTreeMiddle(
                            rightPoint,
                            midCurve,
                            rightHeight,
                            midTrailingPoints,
                            outputTrailingPoints,
                            outputCurve,
                            copyOp
                        );
                        // we imagine that this would have copied out, if it needed to, in the base case
                        //Uncompute the mid points
                        (Adjoint IsogenyTreeMiddle)(
                            leftPoint,
                            startingCurve,
                            leftHeight,
                            [startingPoint] + trailingPoints,
                            [rightPoint] + midTrailingPoints,
                            midCurve,
                            NoOp<ECCoordsMontgomeryFormAPlusC>//will never copy from left tree
                        );
                    }
                    // Clear left point
                    (Adjoint IteratedPointDouble)(startingCurve, startingPoint, rightHeight, leftPoint);
                }
            }
        }
        adjoint auto;
    }

    /// # Summary
    /// Divides the height of a SIKE isogeny tree into two components
    /// for recursion.
    /// Can be optimized for memory/depth trade-offs.
    function OptimalSIKEDivision(height : Int, nTrailingPoints : Int, nQubits : Int, highMemory : Bool) : (Int, Int){
        /// Currently: Low depth, high memory
        if (highMemory){
            return _HighMemorySIKEDivision(height, nTrailingPoints, nQubits);
        } else {
            return _LowMemorySIKEDivision(height, nTrailingPoints, nQubits);
        }
    }
    function _LowMemorySIKEDivision(height : Int, nTrailingPoints : Int, nQubits : Int) : (Int, Int){
        let leftHeight = height/2;
        let rightHeight = height - leftHeight;
        return (leftHeight, rightHeight);
    }

    function _HighMemorySIKEDivision(height : Int, nTrailingPoints : Int, nQubits : Int) : (Int, Int){
        let spaceConstant = 4;
        let sqrtHeight = Round(Sqrt(IntAsDouble(height)));
        let leftHeight = Max([(sqrtHeight * 2)/spaceConstant, 1]);
        let rightHeight = height - leftHeight;
        return (leftHeight, rightHeight);
    }

    /// # Summary
    /// Computes the j-invariant of the curve reached
    /// by an isogeny defined by a quantum secret
    /// SIKE key, given classical parameters for the scheme.
    ///
    /// # Inputs
    /// ## startingCurve
    /// The initial curve for the scheme
    /// ## pointP
    /// A point of exact order 2^e such that 
    /// $[2^{e-1}]P = (0:0:1)$.
    /// ## pointQ
    /// A point of exact order 2^e such that 
    /// $[2^{e-1}]Q \neq (0:0:1)$.
    /// ## pointR
    /// The point equal to $Q - P$
    /// ## height
    /// The exponent e
    /// ## secretKey
    /// Qubit register containing the secret key s,
    /// where the isogeny computed will have kernel
    /// generated by Q + sP
    /// ## outputJInvariant
    /// Blank qubit register to contain the j-invariant of hte
    /// output curv
    operation ComputeSIKETwoIsogeny(
        startingCurve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointR : ECPointMontgomeryXZClassical,
        height : Int,
        secretKey : LittleEndian,
        outputJInvariant : Fp2MontModInt
    ) : Unit {
        body (...){
            (Controlled ComputeSIKETwoIsogeny)(new Qubit[0], (
                startingCurve, 
                pointP, 
                pointQ, 
                pointR, 
                height, 
                secretKey, 
                outputJInvariant)
            );
        }
        controlled (controls, ...){
            let nQubits = Length(outputJInvariant::reals::register!);
            let modulus = outputJInvariant::modulus;
            using (kernelPointQubits = Qubit[4 * nQubits]){
                let kernelPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, kernelPointQubits);
                MontgomeryXZPointLadder(startingCurve, pointP, pointQ, pointR, secretKey, kernelPoint);
                using ((startingCurveQubits, outputCurveQubits) = (Qubit[4 * nQubits], Qubit[4 * nQubits])){
                    let qStartingCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, startingCurveQubits);
                    EncodeECCoordsMontgomeryFormAPlusC(startingCurve, qStartingCurve);
                    let outputCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, outputCurveQubits);
                    IsogenyTreeMiddle(
                        kernelPoint,
                        qStartingCurve,
                        height,
                        new ECPointMontgomeryXZ[0],
                        new ECPointMontgomeryXZ[0],
                        outputCurve,
                        (Controlled GetJInvariantAPlusC)(controls, (_, outputJInvariant))
                    );
                    (Adjoint EncodeECCoordsMontgomeryFormAPlusC)(startingCurve, qStartingCurve);
                }
                (Adjoint MontgomeryXZPointLadder)(startingCurve, pointP, pointQ, pointR, secretKey, kernelPoint);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Recursively computes a power-of-two isogeny
    /// whose kernel is generated by point given as 
    /// input in a quantum register. Uncomputes infrequently,
    /// intended for small base cases.
    /// 
    /// # Inputs
    /// ## startingPoint
    /// The generator of the kernel of the isogeny
    /// ## startingCurve 
    /// The curve which contains the starting point
    /// ## height
    /// The power of two that is the degree of the
    /// isogeny (equivalently, the log in base 2
    /// of the order of the starting point).
    /// ## trailingPoints
    /// An array (possibly empty) of points
    /// also on the curve, which the operation
    /// will map through the isogeny it computes.
    /// ## outputTrailingPoints
    /// The register where the operation will save the output
    /// of each trailingPoint after mapping it through the
    /// isogeny
    /// ## outputCurve
    /// The codomain of the isogeny calculated.
    /// ## copyOp
    /// When the operation finishes, it will call this 
    /// operation on the final outputCurve before 
    /// being uncomputed. 
    ///
    /// # Remarks
    /// For height <= 4, this operation uncomputes nothing;
    /// for larger heights, it recurses in a binary tree, 
    /// uncomputing only the subtrees but not the doublings.
    operation IsogenyTreeSmall(
        startingPoint : ECPointMontgomeryXZ,
        startingCurve : ECCoordsMontgomeryFormAPlusC,
        height : Int,
        trailingPoints : ECPointMontgomeryXZ[],
        outputTrailingPoints : ECPointMontgomeryXZ[],
        outputCurve : ECCoordsMontgomeryFormAPlusC,
        copyOp : (ECCoordsMontgomeryFormAPlusC => Unit is Ctl + Adj)
    ) : Unit {
        body (...){
            let nQubits = Length(startingPoint::xs::reals::register!);
            let modulus = startingPoint::xs::modulus;
            let nTrailingPoints = Length(trailingPoints);
            let (nDoubleAncilla, _) = AncillaCountDoubleECPoint(nQubits);
            if (height == 1){//base case
                if (nTrailingPoints >= 1){
                    CrissCrossFp2ElementMontgomeryForm(startingPoint::xs, startingPoint::zs);
                    using (fanoutQubits = Qubit[4 * nQubits * (nTrailingPoints - 1)]){
                        let pointRegister = 
                                startingPoint::xs::reals::register! 
                                + startingPoint::xs::imags::register! 
                                + startingPoint::zs::reals::register! 
                                + startingPoint::zs::imags::register!;
                        if (nTrailingPoints > 1){
                            FanoutRegister(pointRegister, fanoutQubits);
                        }
                        let pointArray = [startingPoint] + QubitArrayAsECPointArray(nTrailingPoints - 1, nQubits, modulus, fanoutQubits);
                        for (idx in 0.. nTrailingPoints - 1){
                            _TwoIsogenyOfCrossedKernelPoint(pointArray[idx], trailingPoints[idx], outputTrailingPoints[idx]);
                        }
                        if (nTrailingPoints > 1){
                            (Adjoint FanoutRegister)(pointRegister, fanoutQubits);
                        }
                    }
                    (Adjoint CrissCrossFp2ElementMontgomeryForm)(startingPoint::xs, startingPoint::zs);
                }
                TwoIsogenyOfCurveMontgomeryXZ(startingPoint, outputCurve);
                if (nTrailingPoints == 0){// only occurs on the final run!
                    copyOp(outputCurve);
                    // We actually want to uncompute the output curve this time
                    (Adjoint TwoIsogenyOfCurveMontgomeryXZ)(startingPoint, outputCurve);
                }
            } elif (height == 3) {
                using ((pointQubits, 
                    doublingAncillas,
                    curveQubits,
                    trailingPointQubits
                    ) = (
                    Qubit[4 * nQubits * 5], 
                    Qubit[nDoubleAncilla * 2],
                    Qubit[4 * nQubits * 2],
                    Qubit[4 * nQubits * 2 * nTrailingPoints]
                )){
                    let treePoints = QubitArrayAsECPointArray(5, nQubits, modulus, pointQubits);
                    let curves = [
                        QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits[0.. 4 * nQubits - 1]),
                        QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits[4 * nQubits.. 8 * nQubits - 1])
                    ];
                    let doublingAncillaArray = EvenlyPartitionedArray(doublingAncillas, nDoubleAncilla);
                    let midTrailingPoints = [
                        QubitArrayAsECPointArray(nTrailingPoints, nQubits, modulus, trailingPointQubits[0 .. 4 * nQubits * nTrailingPoints - 1]),
                        QubitArrayAsECPointArray(nTrailingPoints, nQubits, modulus, trailingPointQubits[4 * nQubits * nTrailingPoints .. 8 * nQubits * nTrailingPoints - 1])
                    ];
                    ////		Tree:
                    ///        Start
                    ///        /   \
                    ///       1     3
                    ///      / \     \
                    ///     0   2     4
                    DoubleECPointMontgomeryXZOpen(startingPoint, startingCurve, doublingAncillaArray[0], treePoints[0]); /// start -> 1
                    DoubleECPointMontgomeryXZOpen(treePoints[0], startingCurve, doublingAncillaArray[1], treePoints[1]); // 1 -> 0
                    IsogenyTreeSmall(
                        treePoints[1], 
                        startingCurve, 
                        1, 
                        [treePoints[0], startingPoint] + trailingPoints, 
                        [treePoints[2], treePoints[3]] + midTrailingPoints[0], 
                        curves[0], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 1 -> 2; start ->3
                    IsogenyTreeSmall(
                        treePoints[2], 
                        curves[0], 
                        1, 
                        [treePoints[3]] + midTrailingPoints[0], 
                        [treePoints[4]] + midTrailingPoints[1], 
                        curves[1], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 3-> 4

                    IsogenyTreeSmall(treePoints[4], curves[1], 1, midTrailingPoints[1], outputTrailingPoints, outputCurve, copyOp); // finish

                    (Adjoint IsogenyTreeSmall)(
                        treePoints[2], 
                        curves[0], 
                        1, 
                        [treePoints[3]] + midTrailingPoints[0], 
                        [treePoints[4]] + midTrailingPoints[1], 
                        curves[1], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 3-> 4
                    (Adjoint IsogenyTreeSmall)(
                        treePoints[1], 
                        startingCurve, 
                        1, 
                        [treePoints[0], startingPoint] + trailingPoints, 
                        [treePoints[2], treePoints[3]] + midTrailingPoints[0], 
                        curves[0], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 1 -> 2; start ->3
                    (Adjoint DoubleECPointMontgomeryXZOpen)(treePoints[0], startingCurve, doublingAncillaArray[1], treePoints[1]); // 0 -> 1
                    (Adjoint DoubleECPointMontgomeryXZOpen)(startingPoint, startingCurve, doublingAncillaArray[0], treePoints[0]); // start -> 0
                }

            } elif (height == 4) {
                using ((pointQubits, 
                    doublingAncillas,
                    curveQubits,
                    trailingPointQubits
                    ) = (
                    Qubit[4 * nQubits * 8], 
                    Qubit[nDoubleAncilla * 4],
                    Qubit[4 * nQubits * 3],
                    Qubit[4 * nQubits * 3 * nTrailingPoints]
                )){
                    let treePoints = QubitArrayAsECPointArray(8, nQubits, modulus, pointQubits);
                    let curves = [
                        QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits[0.. 4 * nQubits - 1]),
                        QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits[4 * nQubits.. 8 * nQubits - 1]),
                        QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits[8 * nQubits.. 12 * nQubits - 1])
                    ];
                    let doublingAncillaArray = EvenlyPartitionedArray(doublingAncillas, nDoubleAncilla);
                    let midTrailingPoints = [
                        QubitArrayAsECPointArray(nTrailingPoints, nQubits, modulus, trailingPointQubits[0 .. 4 * nQubits * nTrailingPoints - 1]),
                        QubitArrayAsECPointArray(nTrailingPoints, nQubits, modulus, trailingPointQubits[4 * nQubits * nTrailingPoints .. 8 * nQubits * nTrailingPoints - 1]),
                        QubitArrayAsECPointArray(nTrailingPoints, nQubits, modulus, trailingPointQubits[8 * nQubits * nTrailingPoints .. 12 * nQubits * nTrailingPoints - 1])
                    ];
                    ////		Tree:
                    ///        Start
                    ///        /   \
                    ///       2     4
                    ///      /       \
                    ///     1         6
                    ///    / \       / \
                    ///   0   3     5   7
                    DoubleECPointMontgomeryXZOpen (startingPoint, startingCurve, doublingAncillaArray[0], treePoints[2]); // start -> 2
                    DoubleECPointMontgomeryXZOpen (treePoints[2], startingCurve, doublingAncillaArray[1], treePoints[1]); // 2 -> 1
                    DoubleECPointMontgomeryXZOpen (treePoints[1], startingCurve, doublingAncillaArray[2], treePoints[0]); // 1 -> 0
                    IsogenyTreeSmall (
                        treePoints[0], 
                        startingCurve, 
                        1, 
                        [treePoints[1], startingPoint] + trailingPoints, 
                        [treePoints[3], treePoints[4]] + midTrailingPoints[0], 
                        curves[0], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    );//1 -> 3; start -> 4
                    IsogenyTreeSmall (
                        treePoints[3], 
                        curves[0], 
                        1, 
                        [treePoints[4]] + midTrailingPoints[0], 
                        [treePoints[6]] + midTrailingPoints[1], 
                        curves[1], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 4 -> 6
                    DoubleECPointMontgomeryXZOpen (treePoints[6], curves[1], doublingAncillaArray[3], treePoints[5]); // 6 -> 5
                    IsogenyTreeSmall (
                        treePoints[5], 
                        curves[1], 
                        1, 
                        [treePoints[6]] + midTrailingPoints[1], 
                        [treePoints[7]] + midTrailingPoints[2], 
                        curves[2], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 6 -> 7
                    
                    IsogenyTreeSmall(treePoints[7], curves[2], 1, midTrailingPoints[2], outputTrailingPoints, outputCurve, copyOp); //finish

                    (Adjoint IsogenyTreeSmall)(
                        treePoints[5], 
                        curves[1], 
                        1, 
                        [treePoints[6]] + midTrailingPoints[1], 
                        [treePoints[7]] + midTrailingPoints[2], 
                        curves[2], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 6 <- 7
                    (Adjoint DoubleECPointMontgomeryXZOpen)(treePoints[6], curves[1], doublingAncillaArray[3], treePoints[5]); // 6 -> 5
                    (Adjoint IsogenyTreeSmall)(
                        treePoints[3], 
                        curves[0], 
                        1, 
                        [treePoints[4]] + midTrailingPoints[0], 
                        [treePoints[6]] + midTrailingPoints[1], 
                        curves[1], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    ); // 4 -> 6
                    (Adjoint IsogenyTreeSmall)(
                        treePoints[0], 
                        startingCurve, 
                        1, 
                        [treePoints[1], startingPoint] + trailingPoints, 
                        [treePoints[3], treePoints[4]] + midTrailingPoints[0], 
                        curves[0], 
                        NoOp<ECCoordsMontgomeryFormAPlusC>
                    );//1 -> 3; start -> 4
                    (Adjoint DoubleECPointMontgomeryXZOpen)(treePoints[1], startingCurve, doublingAncillaArray[2], treePoints[0]); // 1 -> 0
                    (Adjoint DoubleECPointMontgomeryXZOpen)(treePoints[2], startingCurve, doublingAncillaArray[1], treePoints[1]); // 2 -> 1
                    (Adjoint DoubleECPointMontgomeryXZOpen)(startingPoint, startingCurve, doublingAncillaArray[0], treePoints[2]); // start -> 2
                } 
            } else {
                //here we just do the full tree, no uncomputing mid-way values
                let midHeight = height/2;
                using ((doubledQubits, 
                    isogenyCurveQubits,
                    trailingPointQubits
                    ) = (
                    Qubit[4 * nQubits], 
                    Qubit[4 * nQubits], 
                    Qubit[4 * nQubits * (nTrailingPoints+1)]
                )){
                    let doubledPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, doubledQubits);
                    let isogenyCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, isogenyCurveQubits);
                    let midTrailingPoints = QubitArrayAsECPointArray(nTrailingPoints + 1, nQubits, modulus, trailingPointQubits);
                    IteratedPointDoubleFullMemory(startingCurve, startingPoint, height - midHeight, doubledPoint);
                    IsogenyTreeSmall(doubledPoint, startingCurve, midHeight, [startingPoint] + trailingPoints, midTrailingPoints, isogenyCurve, NoOp<ECCoordsMontgomeryFormAPlusC>);
                    IsogenyTreeSmall(midTrailingPoints[0], isogenyCurve, height- midHeight, midTrailingPoints[1..nTrailingPoints], outputTrailingPoints, outputCurve, copyOp);
                    (Adjoint IsogenyTreeSmall)(doubledPoint, startingCurve, midHeight, [startingPoint] + trailingPoints, midTrailingPoints, isogenyCurve, NoOp<ECCoordsMontgomeryFormAPlusC>);
                    (Adjoint IteratedPointDoubleFullMemory)(startingCurve, startingPoint, height - midHeight, doubledPoint);
                }
            }
        }
        adjoint controlled auto;
    }
}