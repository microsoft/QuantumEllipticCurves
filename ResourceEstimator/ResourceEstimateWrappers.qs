// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.ResourceEstimator
{
    open Microsoft.Quantum.Crypto.Tests.Isogenies;
    open Microsoft.Quantum.Crypto.Fp2Arithmetic;
    open Microsoft.Quantum.Crypto.Isogenies;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Microsoft.Quantum.Crypto.EllipticCurves;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;


    operation ClearRegister(register:Qubit[]):Unit {
        for idx in 0..Length(register)-1 {
            AssertMeasurementProbability([PauliZ],[register[idx]],Zero,0.0,"n/a",0.5);
        }	
        ResetAll(register);
    }

    operation CCNOTEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use qubits = Qubit[3] {
            CCNOT(qubits[0], qubits[1], qubits[2]);
            ClearRegister(qubits);
        }
    }

    operation ControlledOp<'T>(isControlled : Bool, op : ('T => Unit is Ctl), parameters : 'T) : Unit {
        if (isControlled){
            use controls = Qubit[1] {
                (Controlled op)(controls, (parameters));
                ClearRegister(controls);
            }
        } else {
            op(parameters);
        }
    }

    operation QuantumWhileEstimator(nQubits : Int, isControlled : Bool) : Unit {
        //The types are confusing, so this does the control manually
        let logn = BitSizeI(nQubits);
        use kQubits = Qubit[logn +1] {
            let counter = QubitsAsCounter(kQubits);
            counter::Prepare();
            if (isControlled){
                use controls = Qubit[1] {
                    (Controlled QuantumWhile)(controls, (0, nQubits, NoOp<Int>, NoOp<Qubit>, NoOp<Int>, counter));
                    ClearRegister(controls);
                }
            } else {
                QuantumWhile(0, nQubits, NoOp<Int>, NoOp<Qubit>, NoOp<Int>, counter);
            }
            ClearRegister(kQubits);
        }
    }

    operation QuantumWhileAdditionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let logn = BitSizeI(nQubits);
        use (kQubits, xQubits, yQubits) = (Qubit[logn +1], Qubit[nQubits], Qubit[nQubits]) {
            let counter = QubitsAsCounter(kQubits);
            let xs = LittleEndian(xQubits);
            let ys = LittleEndian(yQubits);
            counter::Prepare();
            let AddWithInteger = DummyIntegerWrapper(AddIntegerNoCarry, (xs,ys), _);
            if (isControlled){
                use controls = Qubit[1] {
                    (Controlled QuantumWhile)(controls, (0,nQubits, AddWithInteger, counter::Test, AddWithInteger, counter));
                    ClearRegister(controls);
                }
            } else {
                QuantumWhile(0,nQubits, AddWithInteger, counter::Test, AddWithInteger, counter);
            }
            ClearRegister(kQubits);
        }
    }

    operation LookUpEstimator(nQubits : Int, isControlled : Bool) : Unit {
        if (nQubits < 25){
            use (addressQubits, outputQubits) = (Qubit[nQubits], Qubit[nQubits]) {
                let valueTable = Microsoft.Quantum.Arrays.ForEach(RandomBoundedBigInt(_, 2L^nQubits - 1L ), [0L, size= 2^nQubits]);
                let value = LittleEndian(outputQubits);
                let address = LittleEndian(addressQubits);
                ControlledOp<(BigInt[], (BigInt => Unit is Ctl + Adj), LittleEndian)>
                    (isControlled, EqualLookup<BigInt>, (valueTable, ApplyXorInPlaceL(_, value), address));
                ClearRegister(addressQubits + outputQubits);
            }
        } 
    }

    operation PointLookUpEstimator(nQubits : Int, isControlled : Bool, windowSize : Int) : Unit {
        use (addressQubits, outputXs, outputYs) = (Qubit[windowSize + 1], Qubit[nQubits], Qubit[nQubits]) {
            let points  = RandomPointArray(2L^nQubits - 1L, windowSize) + [RandomInvalidECPoint(false, 2L^nQubits - 1L)];
            let value = ECPointMontgomeryForm(
                MontModInt(2L^nQubits - 1L, LittleEndian(outputXs)),
                MontModInt(2L^nQubits - 1L, LittleEndian(outputYs))
            );
            let address = LittleEndian(addressQubits);
            ControlledOp<(ECPointClassical[], (ECPointClassical => Unit is Ctl + Adj), LittleEndian)>
                (isControlled, EqualLookup<ECPointClassical>, (points, EncodeClassicalECPointInQuantum(_, value), address));
            ClearRegister(addressQubits + outputXs + outputYs);
        }
    }

    operation CheckIfAllZeroEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use (xs,result) = (Qubit[nQubits], Qubit()) {
            ControlledOp(isControlled, CheckIfAllZero, (xs, result));
            ClearRegister(xs+[result]);
        }
    }

    operation CheckIfAllOneEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use (xs,result) = (Qubit[nQubits], Qubit()) {
            ControlledOp(isControlled, CheckIfAllOnes, (xs, result));
            ClearRegister(xs+[result]);
        }
    }

    operation AdditionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[2*nQubits+1] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let carry = register[2*nQubits];
            ControlledOp(isControlled, AddInteger, (xs,ys,carry));
            ClearRegister(register);
        }
    }




    operation AdditionNoCarryEstimator(nQubits:Int, isControlled : Bool):Unit {
        use register = Qubit[2*nQubits] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            ControlledOp(isControlled, AddIntegerNoCarry, (xs,ys));
            ClearRegister(register);
        }
    }


    operation CyclicShiftEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[nQubits] {
            let qInteger = LittleEndian(register[0 .. nQubits - 1]);
            ControlledOp(isControlled, CyclicRotateRegister, (qInteger));
            ClearRegister(register);
        }
    }

    operation ConstantAdditionEstimator(nQubits:Int, isControlled : Bool):Unit {
        use register = Qubit[nQubits] {
            let constant = RandomBigInt(2L^nQubits);
            ControlledOp(isControlled, AddConstant, (constant, LittleEndian(register)));
            ClearRegister(register);
        }
    }



    operation GreaterThanEstimator(nQubits:Int, isControlled : Bool):Unit {
        use register = Qubit[2*nQubits+1] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let result = register[2*nQubits];
            ControlledOp(isControlled, GreaterThanWrapper, (xs,ys,result));
            ClearRegister(register);
        }
    }



    operation ModularDblEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[nQubits] {
            let modulus = 2L * RandomBigInt(2L ^ (nQubits - 1)) + 1L;
            let xs = LittleEndian(register);
            ControlledOp(isControlled, ModularDblConstantModulus, (modulus, xs));
            ClearRegister(register);
        }
    }

    

    operation ModularAdditionEstimator(nQubits:Int, isControlled : Bool):Unit {
        use register = Qubit[2*nQubits] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let modulus = RandomBigInt(2L ^ nQubits);
            ControlledOp(isControlled, ModularAddConstantModulus, (modulus, xs, ys));
            ClearRegister(register);
        }
    } 

    operation MontgomeryWindowedMultiplicationWindowTest(nQubits : Int, isControlled : Bool, windowSize : Int) : Unit {
        let (nAncillas, nOutputs) = AncillaCountModularMulMontgomeryForm(nQubits);
        use (register, ancillas) = (Qubit[3*nQubits], Qubit[nAncillas]) {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let zs = LittleEndian(register[2*nQubits..3*nQubits -1]);
            let modulus = 2L*RandomBigInt(2L^(nQubits - 1)) + 1L;
            let xMMI= MontModInt(modulus, xs);
            let yMMI= MontModInt(modulus, ys);
            let zMMI= MontModInt(modulus, zs);
            ModularMulMontgomeryFormWindowedOpen(windowSize, xMMI, yMMI, ancillas, zMMI);
            ClearRegister(register);
        }
    }

    operation NonWindowedMontgomeryMultiplicationEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[3*nQubits] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let zs = LittleEndian(register[2*nQubits..3*nQubits -1]);
            let modulus = 2L*RandomBigInt(2L^(nQubits - 1)) + 1L;
            let xMMI= MontModInt(modulus, xs);
            let yMMI= MontModInt(modulus, ys);
            let zMMI= MontModInt(modulus, zs);
            let (nAncillas, nOutputs) = AncillaCountModularMulMontgomeryForm(nQubits);
            use ancillas = Qubit[nAncillas] {
                ControlledOp(isControlled, ModularMulMontgomeryFormGeneric(CopyMontModInt(_,zMMI),_, _), (xMMI, yMMI));
                ClearRegister(ancillas);
            }
            ClearRegister(register);
        }
    }

    operation MontgomeryMultiplicationEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[3*nQubits] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let zs = LittleEndian(register[2*nQubits..3*nQubits -1]);
            let modulus = 2L*RandomBigInt(2L^(nQubits - 1)) + 1L;
            let xMMI= MontModInt(modulus, xs);
            let yMMI= MontModInt(modulus, ys);
            let zMMI= MontModInt(modulus, zs);

            ControlledOp(isControlled, ModularMulAndXorMontgomeryForm, (xMMI,yMMI,zMMI));
            ClearRegister(register);
        }
    }

    operation MontgomerySquareEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[2*nQubits] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let zs = LittleEndian(register[nQubits..2*nQubits -1]);
            let modulus = 2L*RandomBigInt(2L^(nQubits - 1)) + 1L;
            let xMMI= MontModInt(modulus, xs);	
            let zMMI= MontModInt(modulus, zs);

            ControlledOp(isControlled, ModularSquMontgomeryFormWindowedGeneric(CopyMontModInt(_, zMMI), _), (xMMI));
            ClearRegister(register);
        }
    }


    operation MontgomeryInversionRoundEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use (u,v,r,s,ms,controls)=(Qubit[nQubits], Qubit[nQubits], Qubit[nQubits+1], Qubit[nQubits+1], Qubit[2*nQubits], Qubit[1]) {
            let us = LittleEndian(u);
            let vs = LittleEndian(v);
            let rs = LittleEndian(r);
            let ss = LittleEndian(s);
            ControlledOp(isControlled, _MontBitGCDRound, (0, us, vs, rs, ss, ms));
            ClearRegister(u+v+r+s+ms+controls);
        }
    }


    operation MontgomeryInversionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[2*nQubits] {
            let xs = LittleEndian(register[0..nQubits-1]);
            let ys = LittleEndian(register[nQubits..2*nQubits-1]);
            let modulus = 2L*RandomBigInt(2L^(nQubits - 1)) + 1L;
            let xMMI= MontModInt(modulus, xs);
            let yMMI= MontModInt(modulus, ys);
            ControlledOp(isControlled, ModularInvertAndCopyMontgomeryForm, (xMMI,yMMI));
            ClearRegister(register);
        }
    }

    operation ModularDivisionEstimator(nQubits : Int, isControlled : Bool):Unit {
        let modulus = 2L * RandomBigInt(2L ^ (nQubits - 1)) + 1L;
        use (xs, ys, zs)=(Qubit[nQubits], Qubit[nQubits], Qubit[nQubits]) {
            ControlledOp(isControlled, ModularDivideAndAddMontgomeryForm, 
                (MontModInt(modulus,LittleEndian(xs)),
                MontModInt(modulus,LittleEndian(ys)),
                MontModInt(modulus,LittleEndian(zs)))
            );
            ClearRegister(xs + ys + zs);
        }
    }

    operation EllipticCurveConstantPointAdditionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        use register = Qubit[2 * nQubits] {
            let modulus = 2l*RandomBigInt(2L^(nQubits-1)) - 1L;
            let pointX = RandomBoundedBigInt(0L, modulus);
            let pointY = RandomBoundedBigInt(0L, modulus);
            let cPoint = ECPointClassical(pointX, pointY,true,modulus);

            let xs = LittleEndian(register[0 .. nQubits - 1]);
            let ys = LittleEndian(register[nQubits .. 2 * nQubits - 1]);

            let qPoint = ECPointMontgomeryForm(MontModInt(modulus,xs),MontModInt(modulus, ys));
            ControlledOp(isControlled, DistinctEllipticCurveClassicalPointAddition, (cPoint, qPoint));

            ClearRegister(register);
        }
    }

    operation RandomInvalidECPoint(dummyBool : Bool, modulus : BigInt) : ECPointClassical {
        return ECPointClassical(RandomBoundedBigInt(0L, modulus),
                RandomBoundedBigInt(0L,modulus),
                true,
                modulus);
    }

    operation RandomPointArray(modulus : BigInt, windowSize : Int) : ECPointClassical[] {
        return Microsoft.Quantum.Arrays.ForEach(RandomInvalidECPoint(_, modulus),
            [false, size = 2^windowSize]
        );
    }

    operation EllipticCurveWindowedPointAdditionLowWidthWindowTest(nQubits : Int, isControlled : Bool, windowSize : Int) : Unit {
        use register = Qubit[2 * nQubits + windowSize] {
            let modulus = 2L*RandomBoundedBigInt(2L^(nQubits - 2), 2L^(nQubits-1)) + 1L;	
            let points = RandomPointArray(modulus, windowSize);
            let xs = LittleEndian(register[0 .. nQubits - 1]);
            let ys = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
            let address = LittleEndian(register[2 * nQubits .. 2 * nQubits + windowSize - 1]);

            let qPoint = ECPointMontgomeryForm(MontModInt(modulus,xs),MontModInt(modulus, ys));
            ControlledOp(isControlled, WindowedEllipticCurvePointAdditionLowWidth, (points, address, qPoint));

            ClearRegister(register);
        }
    }



    operation EllipticCurveWindowedPointAdditionWindowTest(nQubits : Int, isControlled : Bool, windowSize : Int) : Unit {
        use register = Qubit[2 * nQubits + windowSize] {
            let modulus = 2L*RandomBoundedBigInt(2L^(nQubits - 2), 2L^(nQubits-1)) + 1L;	
            let points = RandomPointArray(modulus, windowSize);
            let xs = LittleEndian(register[0 .. nQubits - 1]);
            let ys = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
            let address = LittleEndian(register[2 * nQubits .. 2 * nQubits + windowSize - 1]);

            let qPoint = ECPointMontgomeryForm(MontModInt(modulus,xs),MontModInt(modulus, ys));
            ControlledOp(isControlled, WindowedEllipticCurvePointAddition, (points, address, qPoint));

            ClearRegister(register);
        }
    }

    operation EllipticCurveSignedWindowedPointAdditionWindowTest(nQubits : Int, isControlled : Bool, windowSize : Int) : Unit {
        
        use register = Qubit[2 * nQubits + windowSize] {
            let modulus = 2L*RandomBoundedBigInt(2L^(nQubits - 2), 2L^(nQubits-1)) + 1L;
            Message($"OG modulus: {modulus}");	
            let points = RandomPointArray(modulus, windowSize - 1) + [RandomInvalidECPoint(false, modulus)];
            let xs = LittleEndian(register[0 .. nQubits - 1]);
            let ys = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
            let address = register[2 * nQubits .. 2 * nQubits + windowSize - 1];
            let qPoint = ECPointMontgomeryForm(MontModInt(modulus,xs),MontModInt(modulus, ys));
            ControlledOp(isControlled, SignedWindowedEllipticCurvePointAdditionLowWidth, (points, address, qPoint));

            ClearRegister(register);
        }	
    }

    operation EllipticCurveWindowedPointAdditionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let windowSize = OptimalPointAdditionWindowSize(nQubits);
        EllipticCurveWindowedPointAdditionWindowTest(nQubits, isControlled, windowSize);

    }

    operation EllipticCurveWindowedPointAdditionLowWidthEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let windowSize = OptimalPointAdditionWindowSize(nQubits);
        EllipticCurveWindowedPointAdditionLowWidthWindowTest(nQubits, isControlled, windowSize);
    }

    operation EllipticCurveSignedWindowedPointAdditionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let windowSize = OptimalSignedPointAdditionWindowSize(nQubits);
        EllipticCurveSignedWindowedPointAdditionWindowTest(nQubits, isControlled, windowSize);
    }

    operation FixedEllipticCurveSignedWindowedPointAdditionEstimator(nQubits : Int, isControlled : Bool) : Unit {
        mutable modulus = 0L;
        mutable basePoint = ECPointClassical(0L,0L,false,0L);
        mutable curve = ECCurveWeierstrassClassical(0L, 0L, 0L);
        if (nQubits == 10){
            let (tempCurve, tempPoint, _, _) = TenBitCurve(); 
            set curve = tempCurve;
            set basePoint = tempPoint;
        } elif (nQubits == 30){
            let (tempCurve, tempPoint, _, _) = ThirtyBitCurve(); 
            set curve = tempCurve;
            set basePoint = tempPoint;
        } elif (nQubits == 192){
            let (tempCurve, tempPoint, _, _) = NISTP192(); 
            set curve = tempCurve;
            set basePoint = tempPoint; 
        } elif (nQubits == 224){
            let (tempCurve, tempPoint, _, _) = NISTP224(); 
            set curve = tempCurve;
            set basePoint = tempPoint; 
        } elif (nQubits == 256){
            let (tempCurve, tempPoint, _, _) = NISTP256(); 
            set curve = tempCurve;
            set basePoint = tempPoint; 
        } elif (nQubits == 384){
            let (tempCurve, tempPoint, _, _) = NISTP384(); 
            set curve = tempCurve;
            set basePoint = tempPoint; 
        } elif (nQubits == 521){
            let (tempCurve, tempPoint, _, _) = NISTP521(); 
            set curve = tempCurve;
            set basePoint = tempPoint; 
        } else {
            Fact(false, $"No pre-specified curve exists with {nQubits}-bit modulus");
        }
        set modulus = curve::modulus;
        let windowSize = OptimalPointAdditionWindowSize(nQubits);
        use register = Qubit[2 * nQubits + windowSize] {	
            let points = PointTable(basePoint, 
                ECPointClassical(0L, 0L, false, modulus),
                curve,
                windowSize
            ) + [MultiplyClassicalECPoint(basePoint, curve, 2L^windowSize)];

            let xs = LittleEndian(register[0 .. nQubits - 1]);
            let ys = LittleEndian(register[nQubits .. 2 * nQubits - 1]);
            let address = register[2 * nQubits .. 2 * nQubits + windowSize - 1];

            let qPoint = ECPointMontgomeryForm(MontModInt(modulus,xs),MontModInt(modulus, ys));
            ControlledOp(isControlled, SignedWindowedEllipticCurvePointAdditionLowWidth, (points, address, qPoint));
            ClearRegister(register);
        }

    }

    
    operation DifferentialAddEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = RandomFp2Modulus(nQubits);
        let pointP = ECPointMontgomeryXZClassical(RandomFp2ElementClassical(modulus), RandomFp2ElementClassical(modulus));
        let (nAncillas, _) = AncillaCountECPointDiffAddition(nQubits);
        use (qQubits, qMinPQubits, ancillas, outputQubits) = 
            (Qubit[4 * nQubits], Qubit[4 * nQubits], Qubit[nAncillas], Qubit[4 * nQubits]){
            let pointQ = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, qQubits);
            let pointQminP = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, qMinPQubits);
            let outputPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, DifferentialAddECPointMontgomeryXZOpen, (pointP, pointQ, pointQminP, ancillas, outputPoint));
            ClearRegister(qQubits + qMinPQubits + ancillas + outputQubits);
        }
        
    }

    operation PointDoublingEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = RandomFp2Modulus(nQubits);
        let (nAncillas, _) = AncillaCountDoubleECPoint(nQubits);
        use (pointQubits, curveQubits, ancillas, outputQubits)
            = (Qubit[4 * nQubits], Qubit[4 * nQubits], Qubit[nAncillas], Qubit[4 * nQubits]){
            let point = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, pointQubits);
            let curve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits);
            let outputPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, DoubleECPointMontgomeryXZOpen, (point, curve, ancillas, outputPoint));
            ClearRegister(pointQubits + curveQubits + ancillas + outputQubits);
        }
    }

    operation TwoIsogenyPointEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = RandomFp2Modulus(nQubits);
        use (kernelQubits, targetQubits, outputQubits)
            = (Qubit[4 * nQubits], Qubit[4 * nQubits], Qubit[4 * nQubits]){
            let kernelPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, kernelQubits);
            let targetPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, targetQubits);
            let outputPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, _TwoIsogenyOfCrossedKernelPoint, (kernelPoint, targetPoint, outputPoint));
            ClearRegister(kernelQubits + targetQubits + outputQubits);
        }
    }
    operation TwoIsogenyCurveEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = RandomFp2Modulus(nQubits);
        use (kernelQubits, outputQubits)
            = (Qubit[4 * nQubits], Qubit[4 * nQubits]){
            let kernelPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, kernelQubits);
            let outputCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, TwoIsogenyOfCurveMontgomeryXZ, (kernelPoint, outputCurve));
            ClearRegister(kernelQubits + outputQubits);
        }
    }

    operation SIKEDifferentialAddEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let sikeParams = GetSIKEParams(nQubits/2);
        let modulus = sikeParams::prime;
        let pointP = sikeParams::pointP;
        let (nAncillas, _) = AncillaCountECPointDiffAddition(nQubits);
        use (qQubits, qMinPQubits, ancillas, outputQubits) = 
            (Qubit[4 * nQubits], Qubit[4 * nQubits], Qubit[nAncillas], Qubit[4 * nQubits]){
            let pointQ = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, qQubits);
            let pointQminP = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, qMinPQubits);
            let outputPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, DifferentialAddECPointMontgomeryXZOpen, (pointP, pointQ, pointQminP, ancillas, outputPoint));
            ClearRegister(qQubits + qMinPQubits + ancillas + outputQubits);
        }
        
    }

    function GetSIKEParamsForQubits(nQubits : Int) : SIKEParams {
        mutable parameters = GetSIKEParams(4);
        mutable twoTorsion = 4;
        while (not (BitSizeL(parameters::prime) == nQubits)) {
            set parameters = GetSIKEParams(twoTorsion);
            set twoTorsion = twoTorsion + 1;
            Fact(twoTorsion <= 0x174, $"No SIKE parameters with a prime of exactly {nQubits} bits");
        } 
        return parameters;
    }

    operation SIKEPointDoublingEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = (GetSIKEParamsForQubits(nQubits))::prime;
        let (nAncillas, _) = AncillaCountDoubleECPoint(nQubits);
        use (pointQubits, curveQubits, ancillas, outputQubits)
            = (Qubit[4 * nQubits], Qubit[4 * nQubits], Qubit[nAncillas], Qubit[4 * nQubits]){
            let point = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, pointQubits);
            let curve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits);
            let outputPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, DoubleECPointMontgomeryXZOpen, (point, curve, ancillas, outputPoint));
            ClearRegister(pointQubits + curveQubits + ancillas + outputQubits);
        }
    }


    operation SIKETwoIsogenyCurveEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = (GetSIKEParamsForQubits(nQubits))::prime;
        use (kernelQubits, outputQubits)
            = (Qubit[4 * nQubits], Qubit[4 * nQubits]){
            let kernelPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, kernelQubits);
            let outputCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, TwoIsogenyOfCurveMontgomeryXZ, (kernelPoint, outputCurve));
            ClearRegister(kernelQubits + outputQubits);
        }
    }
    
    operation SIKETwoIsogenyPointEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = (GetSIKEParamsForQubits(nQubits))::prime;
        use (kernelQubits, outputQubits)
            = (Qubit[4 * nQubits], Qubit[4 * nQubits]){
            let kernelPoint = QubitArrayAsECPointMontgomeryXZ(modulus, nQubits, kernelQubits);
            let outputCurve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, outputQubits);
            ControlledOp(isControlled, TwoIsogenyOfCurveMontgomeryXZ, (kernelPoint, outputCurve));
            ClearRegister(kernelQubits + outputQubits);
        }
    }

    operation SIKEJInvariantEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let modulus = (GetSIKEParamsForQubits(nQubits))::prime;
        let (nAncillas, _) = AncillaCountJInvariantAPlusC(nQubits);
        use (curveQubits, ancillas, jInvariantQubits) = (Qubit[4 * nQubits], Qubit[nAncillas], Qubit[2 * nQubits]) {
            let curve = QubitArrayAsECCoordsMontgomeryFormAPlusC(modulus, nQubits, curveQubits);
            let jInvariant = QubitArrayAsFp2MontModInt(modulus, jInvariantQubits);
            ControlledOp(isControlled, GetJInvariantAPlusCOpen, (curve, ancillas, jInvariant));
            ClearRegister(curveQubits + ancillas + jInvariantQubits);
        }
    }

    operation SIKEIsogenyEstimator(nQubits : Int, isControlled : Bool) : Unit {
        // Here we assume we're not simulating this, 
        // so we really don't care what the actual values are
        let modulus = RandomFp2Modulus(nQubits);
        let curve = ECCoordsMontgomeryFormAPlusCClassical(RandomFp2ElementClassical(modulus), RandomFp2ElementClassical(modulus));
        let pointP = ECPointMontgomeryXZClassical(RandomFp2ElementClassical(modulus), RandomFp2ElementClassical(modulus));
        let pointQ = ECPointMontgomeryXZClassical(RandomFp2ElementClassical(modulus), RandomFp2ElementClassical(modulus));
        let pointR = ECPointMontgomeryXZClassical(RandomFp2ElementClassical(modulus), RandomFp2ElementClassical(modulus));
        let height = nQubits/2;
        use (coefficientQubits, jQubits) = (Qubit[height], Qubit[2 * nQubits]) {
            let coefficient = LittleEndian(coefficientQubits);
            let jInvariant = QubitArrayAsFp2MontModInt(modulus, jQubits);
            ControlledOp(isControlled, ComputeSIKETwoIsogeny, (curve, pointP, pointQ, pointR, height, coefficient, jInvariant));
            ClearRegister(coefficientQubits + jQubits);
        }
    }

    operation SIKEIsogenyValidPrimeEstimator(nQubits : Int, isControlled : Bool) : Unit {
        let parameters = GetSIKEParamsForQubits(nQubits);
        let modulus = parameters::prime;
        let height = parameters::twoOrder;
        let curve = ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(modulus, 8L, 0L),
            Fp2ElementClassical(modulus, 4L, 0L)
        );
        use (coefficientQubits, jQubits) = (Qubit[height], Qubit[2 * nQubits]) {
            let coefficient = LittleEndian(coefficientQubits);
            let jInvariant = QubitArrayAsFp2MontModInt(modulus, jQubits);
            ControlledOp(isControlled, ComputeSIKETwoIsogeny, 
                (curve, parameters::pointP, parameters::pointQ, 
                    parameters::pointR, height, coefficient, 
                    jInvariant)
            );
            ClearRegister(coefficientQubits + jQubits);
        }
    }
    
}
