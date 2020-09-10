// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.EllipticCurves {
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.ModularArithmetic.DebugHelpers;

    

    ///////////////////////////////////////////////////////////////////////////////////////////////
    //////                                                                                  ///////
    //////                          Elliptic Curves                                         ///////
    //////                                                                                  ///////
    ///////////////////////////////////////////////////////////////////////////////////////////////


    /// # Summary 
    /// A classical data structure for a pseudo-projective elliptic curve
    /// point, where the final coordinate z is `true` for all points
    /// except the point at infinity. `x`=`y`=0 for the point at infinity.
    newtype ECPointClassical = (x : BigInt, y : BigInt, z : Bool, modulus : BigInt);

    /// # Summary 
    /// A quantum data structure for a non-identity elliptic curve
    /// point.
    /// The x and y coordinates are assumed to be in Montgomery form
    /// for R=2^$ with n qubits.
    newtype ECPointMontgomeryForm = (xs : MontModInt, ys : MontModInt);


    newtype ECCurveWeierstrassClassical = (a : BigInt, b : BigInt, modulus : BigInt);

    function TenBitCurve () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 661L;
        let a = 3L;
        let b = 7L;
        let Gx = 474L;
        let Gy = 312L;
        let order = 665L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "10 bit test curve");
    }

    function ThirtyBitCurve () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 1027761563L;
        let a = 3L;
        let b = 7L;
        let Gx = 133353543L;
        let Gy = 964863024L;
        let order = 1027733483L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "30 bit test curve");
    }

    function NISTP192 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 6277101735386680763835789423207666416083908700390324961279L;
        let b = 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1L;
        let a = modulus -3L;
        let Gx = 0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012L;
        let Gy = 0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811L;
        let order = 6277101735386680763835789423176059013767194773182842284081L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "NIST P-192");
    }

    function NISTP224 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 2L^224 - 2L^96 + 1L;
        let b = 18958286285566608000408668544493926415504680968679321075787234672564L;
        let a = modulus - 3L;
        let Gx = 0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21L;
        let Gy = 0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34L;
        let order = 26959946667150639794667015087019625940457807714424391721682722368061L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "NIST P-224");
    }

    function NISTP256 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 115792089210356248762697446949407573530086143415290314195533631308867097853951L;
        let b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bL;
        let a = modulus - 3L;
        let Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296L;
        let Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5L;
        let order = 115792089210356248762697446949407573529996955224135760342422259061068512044369L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "NIST P-256");
    }

    function NISTP384 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319L;
        let b = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aefL;
        let a = modulus - 3L;
        let Gx = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7L;
        let Gy = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5fL;
        let order = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "NIST P-384");
    } 

    function NISTP521 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151L;
        let b = 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00L;
        let a = modulus - 3L;
        let Gx = 0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66L;
        let Gy =0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650L;
        let order = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "NIST P-521");
    }

    function Secp256k1 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String){
        let modulus = 2L^256 - 2L^32 - 2L^9 - 2L^8 - 2L^7 - 2L^6 - 2L^4 - 1L;
        let b = 7L;
        let a = 0L;
        let Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798L;
        let Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8L;
        let order = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141L;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "secp256k1");
    }

    function Curve25519 () : (ECCurveWeierstrassClassical, ECPointClassical, BigInt, String) {
        //Converts from Montgomery to Weierstrass
        let modulus = 2L^255 - 19L;
        let aMontgomery = 486662L;
        let bMontgomery = 1L;
        let xMontgomery = 9L;
        let yMontgomery = 14781619447589544791020593568409986887264606134616475288964881837755586237401L;
        let threeInverse = InverseModL(3L, modulus);
        mutable a = (aMontgomery*aMontgomery * threeInverse) % modulus;
        set a = (modulus - 1L - a) % modulus;
        mutable b = (aMontgomery * threeInverse) % modulus;
        let Gx = (xMontgomery + b) % modulus;
        let Gy = yMontgomery;
        set b = (modulus - b) % modulus;
        set b = (b + 2L * aMontgomery^3 * threeInverse^3) % modulus;
        let order = 8L*(2L^252 + 27742317777372353535851937790883648493L)	;
        return (ECCurveWeierstrassClassical(a, b, modulus), ECPointClassical(Gx, Gy, true, modulus), order, "curve25519");
    }
    
    /// # Summary
    /// Adds two classical elliptic curve points and returns the result.
    ///
    /// # Inputs
    /// ## point1
    /// The first point on the curve.
    /// ## point 2
    /// The second point on the curve
    /// ## curvea
    /// The coefficient a in Weierstrass form, where
    /// the curve is $y^2=x^3+ax+b$.
    ///
    /// # Output
    /// An ECPointClassical point containing point1+point2.
    function AddClassicalECPoint(point1 : ECPointClassical, point2 : ECPointClassical, curvea : BigInt) : ECPointClassical {
        let modulus = point1::modulus;
        mutable lambda = 0L;
        if (not point1::z){
            return point2;
        }
        if (not point2::z){
            return point1;
        }
        if (point1::x==point2::x){
            if ((point1::y+point2::y)%modulus == 0L ){
                return ECPointClassical(0L, 0L, false, modulus);
            }
            set lambda = ((3L * point1::x * point1::x + curvea) * InverseModL(2L * point1::y, modulus))%modulus;
        } else {
            set lambda = ((point1::y - point2::y) * InverseModL(point1::x - point2::x, modulus))%modulus;
        }
        let newx = (lambda ^ 2 - point1::x - point2::x)%modulus;
        let newy = (lambda * (point1::x - newx) - point1::y)%modulus;
        if (newx<0L){
            if (newy<0L){
                return ECPointClassical(newx+modulus, newy + modulus, true, modulus);
            } else {
                return ECPointClassical(newx+modulus, newy, true, modulus);
            } 
        } elif (newy<0L) {
            return ECPointClassical(newx, newy + modulus, true, modulus);
        }
        return ECPointClassical(newx, newy, true, modulus);
    }

    function MultiplyClassicalECPoint(point : ECPointClassical, curve : ECCurveWeierstrassClassical, coefficient : BigInt) :
        ECPointClassical {
        mutable outputPoint = ECPointClassical(0L, 0L, false, curve::modulus);
        let nBits = BitSizeL(coefficient);
        mutable remainingCoefficient = coefficient;
        mutable doubledPoint = point;
        let coefficientBools = BigIntAsBoolArray(coefficient);
        for (idx in 0 .. Length(coefficientBools) - 1){	
            if (coefficientBools[idx]){
                set outputPoint = AddClassicalECPoint(outputPoint, doubledPoint, curve::a);
            }
            set doubledPoint = AddClassicalECPoint(doubledPoint, doubledPoint, curve::a);
        }
        return outputPoint;
    }


    function PointTable(
        generator : ECPointClassical, 
        initialPoint : ECPointClassical,
        curve : ECCurveWeierstrassClassical,
        tableSize : Int
    ) : ECPointClassical[] {
        if (tableSize == 1){
            return [
                initialPoint,
                AddClassicalECPoint(initialPoint, generator, curve::a)
            ];
        } else {
            let points = PointTable(generator, initialPoint, curve, tableSize - 1);
            return points + PointTable(
                generator, 
                AddClassicalECPoint(generator, points[2^(tableSize-1)-1],curve::a), 
                curve, 
                tableSize - 1
            );
        }
    }



    /// # Summary
    /// Takes a classical elliptic curve point and quantum registers
    /// and encodes the point into the quantum registers in Montgomery form
    /// with multiply 2^n (where n is the number of qubits).
    ///
    /// # Inputs
    /// ## point
    /// A classical elliptic curve point.
    /// ## register
    /// Qubit register assumed to be all 0s.
    ///
    /// # Output
    /// ## ECPointMontgomeryForm
    /// References the qubit reigster containing the newly created 
    /// elliptic curve point.
    ///
    /// # Remarks
    /// Inernally divides `register` into x and y components
    operation ClassicalECPointToQuantum(point : ECPointClassical, register : Qubit[]) : ECPointMontgomeryForm {
        body (...){
            Fact(point::z, "Cannot encode the identity point into quantum registers");
            let nQubits = BitSizeL(point::modulus);
            Fact(2 * nQubits <= Length(register),
                $"Points on a curve over {point::modulus} need at least {2 * nQubits} qubits,
                  only {Length(register)} given"
            );
            let ys = LittleEndian(register[0..nQubits - 1]);
            let xs = LittleEndian(register[nQubits..2 * nQubits - 1]);
            let yMont = CreateBigIntInMontgomeryForm(point::modulus, point::y, ys);
            let xMont = CreateBigIntInMontgomeryForm(point::modulus, point::x, xs); 
            return ECPointMontgomeryForm(xMont, yMont);
        }
    }

    /// # Summary
    /// Writes a classical point to a quantum register, which is assumed to be 0.
    /// Encodes the point values into Montgomery form. The quantum register
    /// must be formatted to lie on the same curve as the input point.
    ///
    /// # Inputs
    /// ## inputPoint
    /// Classical point to write
    /// ## outputPoint
    /// Quantum register to write into
    operation EncodeClassicalECPointInQuantum(inputPoint : ECPointClassical, outputPoint : ECPointMontgomeryForm) : Unit {
        body (...) {
            (Controlled EncodeClassicalECPointInQuantum)(new Qubit[0], (inputPoint, outputPoint));
        }
        controlled (controls, ...){
            Fact(inputPoint::modulus == outputPoint::xs::modulus,
                 $"Points are defined over different moduli: {inputPoint::modulus} for
                 the classical point but {outputPoint::xs::modulus} for the quantum point"
            );
            (Controlled EncodeBigIntInMontgomeryForm)(controls, (inputPoint::x, outputPoint::xs));
            (Controlled EncodeBigIntInMontgomeryForm)(controls, (inputPoint::y, outputPoint::ys));
        }
        adjoint controlled auto;
    }

    /// # Summary
    /// Measures a quantum elliptic curve point and 
    /// returns the result as a classical point, 
    /// decoding the Montgomery encoding and resetting the 
    /// qubits to 0.
    ///
    /// # Inputs
    /// ## point
    /// A quantum elliptic curve point.
    ///
    /// # Output
    /// ## ECPointClassical
    /// Classical elliptic curve point with the measured
    /// value.
    operation MeasureECPoint(point : ECPointMontgomeryForm) : ECPointClassical {
        let modulus = point::xs::modulus;
        let nQubits = Length(point::xs::register!);
        let montR = ModPowL(2L, IntAsBigInt(nQubits), modulus);
        let montInv= InverseModL(montR, point::xs::modulus);
        let x = MeasureMontgomeryInteger(point::xs);
        let y = MeasureMontgomeryInteger(point::ys);
        return ECPointClassical(x, y, true, modulus);
    }


    /// # Summary
    /// Given an x-coordinate of an elliptic curve and the 
    /// parameters of the curve, returns an elliptic curve point
    /// with that x-coordinate if it exists; otherwise it 
    /// returns the point at infinity.
    ///
    /// # Inputs
    /// ## x
    /// The x-coordinate of the desired point.
    /// ## a
    /// The value of a of the Weierstrass form of the curve : 
    /// $y^2=x^3+ax+b$.
    /// ## b
    /// The value of b in the Weierstrass form.
    /// ## modulus
    /// The prime modulus of the curve.
    /// ## sign
    /// If true, it flips the sign of the computed y-value of the coordinate
    ///
    /// # Outputs
    /// An ECPointClassical containing the new point.
    ///
    /// # Remarks
    /// To compute the square root, this function exponentiates, which 
    /// only returns the square root if modulus=3 mod 4. 
    function GetECPoint(x : BigInt, a : BigInt, b : BigInt, modulus : BigInt, sign : Bool) : ECPointClassical {
        Fact((modulus) % 4L == 3L, "Implement Tonelli-Shanks if you want to use p!=3 mod 4");
        let ysq= (x^3 + a*x + b)%modulus;
        let y = ModPowL(ysq, (modulus + 1L) / 4L, modulus);
        //test if y is the squre root
        let ysqtest = (y ^ 2) % modulus;
        if (not (ysqtest == ysq)){
            return ECPointClassical(0L, 0L, false, modulus);
        }
        if (sign){
            return ECPointClassical(x, (modulus - y) % modulus, true, modulus);
        } else {
            return ECPointClassical(x, y, true, modulus);
        }
    }

    /// # Summary
    /// Returns a random point on an elliptic curve y^2 = x^3 + ax + b such that it is not 
    /// the identity point 
    /// 
    /// # Inputs
    /// ## a
    /// The coefficient a of the curve
    /// ## b
    /// The coefficient b of the curve
    /// ## modulus
    /// The prime defining the field of the curve
    operation RandomNonInfinityECPoint(a : BigInt, b : BigInt, modulus : BigInt) : ECPointClassical {
        mutable point = ECPointClassical(0L, 0L, false, modulus);
        repeat {
            let signInt = Microsoft.Quantum.Random.DrawRandomInt(0,1);
            if (signInt == 0){
                set point = GetECPoint(RandomBigInt(modulus), a, b, modulus, false);
            } else {
                set point = GetECPoint(RandomBigInt(modulus), a, b, modulus, true);
            }
        } until (point::z);
        return point;
    }

    /// # Summary
    /// Adds two distinct quantum elliptic curve points in place, 
    /// saving the new point to the second register.
    ///
    /// # Inputs
    /// ## point1
    /// The first point, which will be returned unchanged.
    /// ## point2
    /// The second point which will be replaced with the sum.
    ///
    /// # Reference
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remarks
    /// This operation only works correctly under the following conditions : 
    ///     * `point2` does not equal `point1`
    ///     * `point2` does not equal -`point1`
    ///     * `point1`+`point2` does not equal `-point1
    operation DistinctEllipticCurvePointAddition(point1 : ECPointMontgomeryForm, point2 : ECPointMontgomeryForm) : Unit {
        body (...){
            (Controlled DistinctEllipticCurvePointAddition)(new Qubit[0], (point1, point2));
        }
        controlled (controls, ...){
            let nQubits = Length(point1::xs::register!);
            let modulus = point1::xs::modulus;
            // Set the second point to x2-x1 and y2-y1
            (Adjoint ModularAddMontgomeryForm)(point1::xs, point2::xs);
            (Adjoint Controlled ModularAddMontgomeryForm)(controls, (point1::ys, point2::ys));

            using (lambdaqubits = Qubit[nQubits]){
                let lambdas = MontModInt(modulus, LittleEndian(lambdaqubits));
                //Computes lambda in a new register
                (Controlled ModularDivideAndAddMontgomeryForm)(controls, (point2::xs, point2::ys, lambdas));
                //Clears y2-y1 using lambda and x2-x1
                ModularMulAndXorMontgomeryForm(point2::xs, lambdas, point2::ys);
                //Adds 3x1 to x2-x1 to get x2+2x1
                ModularAddMontgomeryForm(point1::xs, point2::xs);
                ModularDblMontgomeryForm(point1::xs);
                ModularAddMontgomeryForm(point1::xs, point2::xs);
                //Adds lambda^2 to x2+2x1 to get x1-x3
                (Adjoint ModularSquMontgomeryFormWindowedGeneric)(ModularAddMontgomeryForm(_, point2::xs), lambdas);
                //Multiplies lambda by x1-x3 and adds the result to the (empty) y register
                ModularMulAndAddMontgomeryForm(point2::xs, lambdas, point2::ys);
                //Uncomputes lambda
                (Adjoint Controlled ModularDivideAndAddMontgomeryForm)(controls, (point2::xs, point2::ys, lambdas));
            }
            //Subtracts 2x1 from the x register
            (Adjoint ModularAddMontgomeryForm)(point1::xs, point2::xs);
            //Halves x1
            (Adjoint ModularDblMontgomeryForm)(point1::xs);
            //Subtracts y1 from the y register to get the new y
            (Adjoint Controlled ModularAddMontgomeryForm)(controls, (point1::ys, point2::ys));
            //Contralled add x1 to the x register and negates
            (Controlled ModularAddMontgomeryForm)(controls, (point1::xs, point2::xs));
            (Controlled ModularNegMontgomeryForm)(controls, (point2::xs));
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Adds a fixed, classical elliptic curve point to
    /// to a quantum point, replacing the value in the 
    /// quantum registers.
    ///
    /// # Inputs
    /// ## point1
    /// The classical point.
    /// ## point2
    /// The quantum point which will be replaced with the sum.
    ///
    /// # Reference
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remarks
    /// This operation only works correctly under the following conditions : 
    ///     * `point2` does not equal `point1`
    ///     * `point2` does not equal -`point1`
    ///     * `point1`+`point2` does not equal `-point1`
    operation DistinctEllipticCurveClassicalPointAddition(point1 : ECPointClassical, point2 : ECPointMontgomeryForm) : Unit {
        body (...){
            (Controlled DistinctEllipticCurveClassicalPointAddition)(new Qubit[0], (point1, point2));
        }
        controlled (controls, ...){
            if (point1::z){
                let nQubits = Length(point2::xs::register!);
                let modulus = point1::modulus;
                // Set the second point to x2-x1 and y2-y1
                (Adjoint ModularAddConstantMontgomeryForm)(point1::x, point2::xs);
                (Adjoint Controlled ModularAddConstantMontgomeryForm)(controls, (point1::y, point2::ys));
                using (lambdaqubits = Qubit[nQubits]){
                    let lambdas = MontModInt(modulus, LittleEndian(lambdaqubits));
                    (Controlled ModularDivideAndAddMontgomeryForm)(controls, (point2::xs, point2::ys, lambdas));
                    //Clears y2-y1 using lambda and x2-x1
                    ModularMulAndXorMontgomeryForm(point2::xs, lambdas, point2::ys);
                    //Adds 3x1 to x2-x1 to get x2+2x1
                    ModularAddConstantMontgomeryForm((3L * point1::x) % modulus, point2::xs);
                    //Adds lambda^2 to x2+2x1 to get x1-x3
                    (Adjoint ModularSquMontgomeryFormWindowedGeneric)(ModularAddMontgomeryForm(_, point2::xs), lambdas);
                    //Multiplies lambda by x1-x3 and adds the result to the (empty) y register
                    ModularMulAndAddMontgomeryForm(point2::xs, lambdas, point2::ys);
                    //Uncomputes lambda
                    (Adjoint Controlled ModularDivideAndAddMontgomeryForm)(controls, (point2::xs, point2::ys, lambdas));
                }
                //Adds y1 to the y register to get the new y
                (Adjoint Controlled ModularAddConstantMontgomeryForm)(controls, (point1::y, point2::ys));
                //Subtracts x1 from the x register and negates
                //Here we need to subtract 2x1 if the addition was controlled, but only one x1 if not controlled
                //So we subtract 2x1 first, then add back x1 with the controls
                (Adjoint ModularAddConstantMontgomeryForm)((2L * point1::x) % modulus, point2::xs);
                (Controlled ModularAddConstantMontgomeryForm)(controls, (point1::x, point2::xs));
                (Controlled ModularNegMontgomeryForm)(controls, (point2::xs));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Writes a classical point to an elliptic curve, including an extra qubit to represent the z-cooordinate
    ///
    /// # Inputs
    /// ## inputPoint
    /// Classical point to write
    /// ## outputPoint
    /// Qubit register to write into (assumed to be zeros)
    /// ## outputZ
    /// A qubit representing whether the point is the identity (|0>) or not (|1>)
    ///
    /// # Remarks
    /// This has nearly identical function to ClassicalECPointToQuantum, except for the z qubit, 
    /// as this is intended for use in windowed point addition
    operation ECPointWrite (inputPoint : ECPointClassical, outputPoint : ECPointMontgomeryForm, outputZ : Qubit) : Unit {
        body (...){
            (Controlled ECPointWrite)(new Qubit[0], (inputPoint, outputPoint, outputZ));
        }
        controlled (controls, ...){
            let modulus = inputPoint::modulus;
            let nQubits = BitSizeL(modulus);
            // Message($"Modulus: {modulus}, nqubits : {nQubits}");
            // Fact(Length(register) >= 2 * nQubits + 1, $"Not enough qubits to write a point; need 2*{nQubits}+1, only has {Length(register)}");
            // if (Length(register) > 2 * nQubits + 1){
            // 	Message($"Warning: too many qubits for an elliptic curve point (given {Length(register)}, needed {2 * nQubits + 1})");
            // }
            if (inputPoint::z){
                //point is the identity: just write the bonus qubit
                CheckIfAllOnes(controls, outputZ);
            }
            (Controlled EncodeBigIntInMontgomeryForm)(controls, (inputPoint::y, outputPoint::ys));
            (Controlled EncodeBigIntInMontgomeryForm)(controls, (inputPoint::x, outputPoint::xs));
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Encodes an array of classical elliptic curve points into ancilla register according to
    /// an address register, than adds that register (possibly in superposition) all to a quantum point.
    /// This has the effect of entangling the address with the final point sum.
    ///
    /// # Inputs
    /// ## points
    /// Array of classical points that will be indexed.
    /// ## address
    /// Quantum register containing the address of the point(s) to add
    /// ## point
    /// The quantum register which will have a point added to it, in place.
    ///
    /// # Remarks
    /// The intent here is that if we want to add many points into a register in superposition, 
    /// we can save by "filling up" an ancilla register with the superposition, then adding all 
    /// these points "at once" with a single fully-quantum point addition.
    operation WindowedEllipticCurvePointAddition(points : ECPointClassical[], address : LittleEndian, point : ECPointMontgomeryForm) : Unit {
        body (...){
            (Controlled WindowedEllipticCurvePointAddition)(new Qubit[0], (points, address, point));
        }
        controlled (controls, ...){
            let modulus = point::xs::modulus;
            let nQubits = Length(point::xs::register!);

            using (ancillaPointQubits = Qubit[2 * nQubits + 1]){
                //Format new qubits into a point
                let ancillaPoint = ECPointMontgomeryForm(
                    MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1])),
                    MontModInt(modulus, LittleEndian(ancillaPointQubits[nQubits .. 2 * nQubits - 1]))
                );
                let zQubit = ancillaPointQubits[2 * nQubits];
                //Write the points in
                (Controlled EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, zQubit), address));
                //Do the addition (in superposition)
                (Controlled DistinctEllipticCurvePointAddition)([zQubit], (ancillaPoint, point));
                //Erase the ancilla point
                //Write the points in
                (Controlled Adjoint EqualLookup)(controls, (points, ECPointWrite(_,ancillaPoint, zQubit), address));
            }
        }
        controlled adjoint auto;
    }

    


    /// # Summary
    /// Writes just the x-coordinate of an elliptic curve times 3,
    /// modulo the prime, into a quantum register. 
    /// Used for the middle step of windowed point addition as part of the
    /// QRAM look-up.
    ///
    /// # Inputs
    /// ## point
    /// A classical elliptic curve point (x,y)
    /// ## xs
    /// Quantum register which should be written as 3x
    ///
    /// # Remarks
    /// To avoid errors in a blank table, this does nothing with a "blank"
    /// classical point (one where the modulus is 0)
    operation _ClassicalECPointFormat(point : ECPointClassical, xs : MontModInt) : Unit {
        body (...) {
            if (point::modulus > 0L){
                let xNew = (point::x * 3L) % point::modulus;
                EncodeBigIntInMontgomeryForm(xNew, xs);
            }
        }
        controlled adjoint auto;
    }

    function OptimalPointAdditionWindowSize(nQubits : Int) : Int {
        return Min([nQubits, 8]);
        // wild guess
        // let logn =  Ceiling(Log(IntAsDouble(nQubits)) / Log(2.0));
        // let loglogn = Ceiling(Log(IntAsDouble(logn)) / Log(2.0));
        // return Min([logn + loglogn + 9, nQubits]);
    }

    /// # Summary
    /// Uses an address register to "look up" which classical point to add
    /// to a quantum point, then does that addition. 
    /// To avoid extra registers, this operation does a "QRAM lookup" that
    /// adds the classical points directly into the quantum registers.
    ///
    /// # Inputs
    /// ## points
    /// Array of classical points that will be indexed.
    /// ## address
    /// Quantum register containing the address of the point(s) to add
    /// ## point
    /// The quantum register which will have a point added to it, in place.
    ///
    /// # Remarks
    /// This should have the same action as `WindowedEllipticCurvePointAddition`,
    /// but should use fewer qubits.
    operation WindowedEllipticCurvePointAdditionLowWidth(points : ECPointClassical[], address : LittleEndian, point : ECPointMontgomeryForm) : Unit {
        body (...){
            (Controlled WindowedEllipticCurvePointAdditionLowWidth)(new Qubit[0], (points, address, point));
        }
        controlled (controls, ...){
            let modulus = point::xs::modulus;
            let nQubits = Length(point::xs::register!);
            using (zQubit = Qubit()){
                // Set the second point to x2-x1 and y2-y1
                // This requires a QRAM look-up
                // Here we also set the zQubit (which controls other operations)
                using (ancillaPointQubits = Qubit[2 * nQubits + 1]){
                    let ancillaPoint = ECPointMontgomeryForm(
                        MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1])),
                        MontModInt(modulus, LittleEndian(ancillaPointQubits[nQubits .. 2 * nQubits - 1]))
                    );
                    let ancillaZ = ancillaPointQubits[2 * nQubits];
                    (Controlled EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, ancillaZ), address));
                    (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::xs, point::xs));
                    (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::ys, point::ys));
                    (Controlled CNOT)(controls, (ancillaZ, zQubit));				
                    (Controlled Adjoint EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, ancillaZ), address));
                }
                using (lambdaqubits = Qubit[nQubits]){
                    let lambdas = MontModInt(modulus, LittleEndian(lambdaqubits));
                    (Controlled ModularDivideAndAddMontgomeryForm)(controls + [zQubit], (point::xs, point::ys, lambdas));
                    //Clears y2-y1 using lambda and x2-x1
                    ModularMulAndXorMontgomeryForm(point::xs, lambdas, point::ys);
                    //Adds 3x1 to x2-x1 to get x2+2x1
                    //This needs another QRAM look-up
                    using (ancillaPointQubits = Qubit[nQubits]){
                        let xsMMI = MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1]));
                        (Controlled EqualLookup)(controls, (points, _ClassicalECPointFormat(_, xsMMI), address));
                        (Controlled ModularAddMontgomeryForm)(controls, (xsMMI, point::xs));
                        (Controlled Adjoint EqualLookup)(controls, (points, _ClassicalECPointFormat(_, xsMMI), address));
                    }
                    //Adds lambda^2 to x2+2x1 to get x1-x3
                    (Adjoint ModularSquMontgomeryFormWindowedGeneric)(ModularAddMontgomeryForm(_, point::xs), lambdas);
                    //Multiplies lambda by x1-x3 and adds the result to the (empty) y register
                    ModularMulAndAddMontgomeryForm(point::xs, lambdas, point::ys);
                    //Uncomputes lambda
                    (Adjoint Controlled ModularDivideAndAddMontgomeryForm)(controls + [zQubit], (point::xs, point::ys, lambdas));
                }
                // Adds all required constants in one go
                using (ancillaPointQubits = Qubit[2 * nQubits + 1]){
                    let ancillaPoint = ECPointMontgomeryForm(
                        MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1])),
                        MontModInt(modulus, LittleEndian(ancillaPointQubits[nQubits .. 2 * nQubits - 1]))
                    ); 
                    let ancillaZ = ancillaPointQubits[2 * nQubits];
                    (Controlled EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, ancillaZ), address));
                    // While the point is in memory: We want to add it as necessary, and control the negation
                    // of x based on the z qubit, which will be uncomputed just after
                    (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::xs, point::xs));
                    (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::ys, point::ys));
                    (Controlled ModularNegMontgomeryForm)(controls + [zQubit], (point::xs));
                    (Controlled CNOT)(controls, (ancillaZ, zQubit));
                    (Controlled Adjoint EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, ancillaZ), address));
                }
            }
        }
        controlled adjoint auto;
    }

    function OptimalSignedPointAdditionWindowSize(nQubits : Int) : Int {
        return Min([nQubits, 8]);
        // wild guess
        // let logn =  Ceiling(Log(IntAsDouble(nQubits)) / Log(2.0));
        // let loglogn = Ceiling(Log(IntAsDouble(logn)) / Log(2.0));
        // return Min([logn + loglogn + 10, nQubits]);
    }

    /// # Summary
    /// Adds a point from a classical array of points to a quantum register. 
    /// The classical point is indexed by a quantum address register, where the 
    /// last qubit of the address is a "sign" bit that, if zero, will flip the sign 
    /// of the point being added and flip all bits of the address (i.e., to 
    /// address the points in reverse order)
    ///
    /// # Inputs
    /// ## points
    /// An array of classical points, assumed to not contain the identity
    /// ## address
    /// Address qubits, where the last qubit is the sign bit
    /// ## point
    /// Quantum register to add the point into
    ///
    /// # Remarks
    /// The intended use is that the point array contains [P,2P,...,2^kP]
    /// for a (k+1)-bit address. With an address of b=(b',b0), we look up 
    /// the point b'P (if b0=1), and if b0=0, we look up the point (2^k-b')P
    /// and flip it to (b'-2^k)P. The overall effect is that we end up adding
    /// [b - 2^k]P to the register.
    operation SignedWindowedEllipticCurvePointAdditionLowWidth(points : ECPointClassical[], address : Qubit[], point : ECPointMontgomeryForm) : Unit {
        body (...){
            (Controlled SignedWindowedEllipticCurvePointAdditionLowWidth)(new Qubit[0], (points, address, point));
        }
        controlled (controls, ...){
            using (addressAncilla = Qubit()){
                let addressLength = Length(address);
                let unsignedAddress = address[0 .. addressLength - 2];
                let leftAddress = LittleEndian(unsignedAddress + [addressAncilla]);
                let signQubit = address[addressLength - 1];
                // we want negative numbers when signQubit = 0
                X(signQubit);
                let modulus = point::xs::modulus;
                let nQubits = Length(point::xs::register!);
                // This flips the ordering of addresses when the sign is negative
                // And increments them
                (Controlled ApplyToEachWrapperCA)([signQubit], (X, unsignedAddress));
                (Controlled Increment)([signQubit], (leftAddress));
                // Set the second point to x2-x1 and y2-y1
                // This requires a QRAM look-up
                // Here we also set the zQubit (which controls other operations)
                if (nQubits > 50){Message($"{nQubits}-bit modulus: First look-up");}
                using (zQubit = Qubit()){
                    using (ancillaPointQubits = Qubit[2 * nQubits]){
                        let ancillaPoint = ECPointMontgomeryForm(
                            MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1])),
                            MontModInt(modulus, LittleEndian(ancillaPointQubits[nQubits .. 2 * nQubits - 1]))
                        );
                        //Look up the point
                        (Controlled EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, zQubit), leftAddress));
                        // Negate the point if the sign bit says so
                        (Controlled ModularNegMontgomeryForm)([signQubit], (ancillaPoint::ys));
                        // Add into the register
                        (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::xs, point::xs));
                        (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::ys, point::ys));
                        // Clear 
                        (Controlled ModularNegMontgomeryForm)([signQubit], (ancillaPoint::ys));
                        (Controlled Adjoint EqualLookup)(controls, (points, EncodeClassicalECPointInQuantum(_, ancillaPoint), leftAddress));
                    }
                    using (lambdaqubits = Qubit[nQubits]){
                        let lambdas = MontModInt(modulus, LittleEndian(lambdaqubits));
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: First division");}
                        (Controlled ModularDivideAndAddMontgomeryForm)(controls + [zQubit], (point::xs, point::ys, lambdas));
                        //Clears y2-y1 using lambda and x2-x1
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: First multiplication");}
                        ModularMulAndXorMontgomeryForm(point::xs, lambdas, point::ys);
                        //Adds 3x1 to x2-x1 to get x2+2x1
                        //This needs another QRAM look-up
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: Second look-up");}
                        using (ancillaPointQubits = Qubit[nQubits]){
                            let xsMMI = MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1]));
                            // Look up 3*(x-value) of the classical point
                            (Controlled EqualLookup)(controls, (points, _ClassicalECPointFormat(_, xsMMI), leftAddress));
                            // Add into the register
                            (Controlled ModularAddMontgomeryForm)(controls, (xsMMI, point::xs));
                            (Controlled Adjoint EqualLookup)(controls, (points, _ClassicalECPointFormat(_, xsMMI), leftAddress));
                        }
                        //Adds lambda^2 to x2+2x1 to get x1-x3
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: Square");}
                        (Adjoint ModularSquMontgomeryFormWindowedGeneric)(ModularAddMontgomeryForm(_, point::xs), lambdas);
                        //Multiplies lambda by x1-x3 and adds the result to the (empty) y register
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: Second multiplication");}
                        ModularMulAndAddMontgomeryForm(point::xs, lambdas, point::ys);
                        //Uncomputes lambda
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: Second division");}
                        (Adjoint Controlled ModularDivideAndAddMontgomeryForm)(controls + [zQubit], (point::xs, point::ys, lambdas));
                    }
                    // Adds all required constants in one go
                    using (ancillaPointQubits = Qubit[2 * nQubits + 1]){
                        if (nQubits > 50){Message($"{nQubits}-bit modulus: Third look-up");}
                        let ancillaPoint = ECPointMontgomeryForm(
                            MontModInt(modulus, LittleEndian(ancillaPointQubits[0..nQubits - 1])),
                            MontModInt(modulus, LittleEndian(ancillaPointQubits[nQubits .. 2 * nQubits - 1]))
                        ); 
                        // Look up the point
                        (Controlled EqualLookup)(controls, (points, EncodeClassicalECPointInQuantum(_, ancillaPoint), leftAddress));
                        // Flip sign if needed
                        (Controlled ModularNegMontgomeryForm)([signQubit], (ancillaPoint::ys));
                        (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::xs, point::xs));
                        (Controlled Adjoint ModularAddMontgomeryForm)(controls, (ancillaPoint::ys, point::ys));
                        // Flip the sign of x (this could be later in the algorithm if needed)
                        (Controlled ModularNegMontgomeryForm)(controls + [zQubit], (point::xs));
                        (Controlled ModularNegMontgomeryForm)([signQubit], (ancillaPoint::ys));
                        (Controlled Adjoint EqualLookup)(controls, (points, ECPointWrite(_, ancillaPoint, zQubit), leftAddress));
                    }
                }
                // Clean up address register
                (Adjoint Controlled Increment)([signQubit], (leftAddress));
                (Controlled ApplyToEachWrapperCA)([signQubit], (X, unsignedAddress));
                X(signQubit);
                // DumpECPointMontgomery(point, "Added accumluator:");
            }
        }
        controlled adjoint auto;
    }
}