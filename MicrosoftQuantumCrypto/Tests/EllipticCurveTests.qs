// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Tests {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Random;

    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.EllipticCurves;

    ///////////////// ELLIPTIC CURVE POINT ADDITION /////////////////
    ///
    /// # Summary
    /// Adds two distinct quantum elliptic curve points in place, 
    /// saving the new point to the second register.
    ///
    /// # Inputs
    /// ## point1
    /// The first point, which will be returned unchanged.
    /// ## point2
    /// The second point, which will be replaced with the sum.
    /// 
    /// # Operations
    /// This can test: 
    ///		* DistinctEllipticCurvePointAddition
   operation EllipticCurveDistinctPointAdditionTestHelper (
        PointAdder : ((ECPointMontgomeryForm, ECPointMontgomeryForm)=>Unit is Ctl), 
        point1 : ECPointClassical, point2 : ECPointClassical, 
        nQubits : Int) : Unit {
      body (...) {
          // Bookkeeping and qubit allocation
            using (register = Qubit[4 * nQubits]) {
                // Write to qubit registers
                mutable qpoint1 = ClassicalECPointToQuantum(point1, register[0..2 * nQubits-1]);
                mutable qpoint2 = ClassicalECPointToQuantum(point2, register[2 * nQubits..4 * nQubits-1]);

                //Run test
                PointAdder(qpoint1, qpoint2);
 
                // Compute expectd classical result
                let expected = AddClassicalECPoint(point1, point2, 0L);
                
                // Check results
                mutable actualp1 = MeasureECPoint(qpoint1);
                Fact(point1::x == actualp1::x and point1::y == actualp1::y and point1::z == actualp1::z, $"Input : Expected {point1!}, got {actualp1!}");
                mutable actualp2 = MeasureECPoint(qpoint2);
                Fact(expected::x == actualp2::x and expected::y == actualp2::y and expected::z == actualp2::z, $"Output : Expected {expected!}, got {actualp2!}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        //Write to qubit registers
                        set qpoint1 = ClassicalECPointToQuantum(point1, register[0..2 * nQubits-1]);
                        set qpoint2 = ClassicalECPointToQuantum(point2, register[2 * nQubits..4 * nQubits-1]);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled PointAdder) (controls, (qpoint1, qpoint2));

                        //Check results
                        set actualp1 = MeasureECPoint(qpoint1);
                        Fact(point1::x == actualp1::x and point1::y == actualp1::y and point1::z == actualp1::z, $"Control 0 : Input : Expected {point1!}, got {actualp1!}");
                        set actualp2 = MeasureECPoint(qpoint2);
                        Fact(point2::x == actualp2::x and point2::y == actualp2::y and point2::z == actualp2::z, $"Control 0 : Output : Expected {point2!}, got {actualp2!}");

                        // Write to qubit registers
                        set qpoint1 = ClassicalECPointToQuantum(point1, register[0..2 * nQubits-1]);
                        set qpoint2 = ClassicalECPointToQuantum(point2, register[2 * nQubits..4 * nQubits-1]);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled PointAdder) (controls, (qpoint1, qpoint2));

                        // Check results
                        set actualp1 = MeasureECPoint(qpoint1);
                        Fact(point1::x == actualp1::x and point1::y == actualp1::y and point1::z == actualp1::z, $"Control 1 : Input : Expected {point1!}, got {actualp1!}");
                        set actualp2 = MeasureECPoint(qpoint2);
                        Fact(expected::x == actualp2::x and expected::y == actualp2::y and expected::z == actualp2::z, $"Control 1 : Output : Expected {expected!}, got {actualp2!}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation EllipticCurveDistinctPointAdditionExhaustiveTestHelper ( 
        PointAdder : ( (ECPointMontgomeryForm, ECPointMontgomeryForm) => Unit is Ctl), 
        nQubits : Int 
    ) : Unit {
        body (...) {
            //Nearly exhaustive list of up to 13-bit primes
            let primes = [
                [0], 
                [2, 3], 
                [5, 7], 
                [11, 13], 
                [17, 19, 23, 29, 31], 
                [37, 41, 43, 47, 53, 59, 61], 
                [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127], 
                [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251], 
                [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509], 
                [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021], 
                [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039], 
                [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093], 
                [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919]
            ];
            Fact(nQubits<=Length(primes), $"The helper does not have {nQubits}-bit primes");
            for (modulus in primes[nQubits-1]) {
                if (modulus % 4 == 3){//necessary for lazy point validation
                    for( curveround in 0 .. modulus - 1 ) {
                        //pick random elliptic curves
                        let ca = DrawRandomInt(0,modulus - 1);
                        let cb = DrawRandomInt(0,modulus - 1);
                        if ((4 * ca^3+27 * cb^2) % modulus != 0) {
                            for (pointround in 0 .. modulus - 1){
                                //pick several points on the curve to test
                                 let p1x = DrawRandomInt(0,modulus - 1);
                                 let p1signint = DrawRandomInt(0,1);
                                 mutable p1signbool = false;
                                 if (p1signint == 1){
                                     set p1signbool = true;
                                 }
                                 let cPoint1 = GetECPoint(IntAsBigInt(p1x), IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus), p1signbool);
                                 //If the randomly chosen x coordinate is not on the curve, 
                                 //then it will return the identity, which has z=false
                                 if (cPoint1::z){
                                     let p2x = DrawRandomInt(0,modulus);
                                     let p2signint = DrawRandomInt(0,1);
                                     mutable p2signbool = false;
                                     if (p2signint == 1){
                                         set p2signbool = true;
                                     }
                                     let cPoint2 = GetECPoint(IntAsBigInt(p2x), IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus), p2signbool);
                                     let cPoint3 = AddClassicalECPoint(cPoint1, cPoint2, IntAsBigInt(ca));
                                     //This checks for exceptional cases : 
                                     //1) Where p2x is not on the curve, so cPoint2 is the identity
                                     //2) Where cPoint1=cPoint2 or cPoint1=-cpoint 2
                                     //3) Where cpoint+cPoint2 = -cPoint1
                                     if (cPoint2::z and cPoint1::x != cPoint2::x and cPoint3::x != cPoint1::x){
                                        EllipticCurveDistinctPointAdditionTestHelper(PointAdder, cPoint1, cPoint2, nQubits);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    operation EllipticCurveDistinctPointAdditionTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 13L;
            let ca = 1L;
            let cb = 7L;
            let cPoint1 = ECPointClassical(1L, 3L, true, modulus);
            let cPoint2 = ECPointClassical(2L, 11L, true, modulus);
            EllipticCurveDistinctPointAdditionTestHelper(DistinctEllipticCurvePointAddition, cPoint1, cPoint2, nQubits);
        }
    }

    operation EllipticCurveDistinctPointAdditionExhaustiveTestReversible() : Unit {
        body(...){
            let nQubits = 4;
            EllipticCurveDistinctPointAdditionExhaustiveTestHelper(DistinctEllipticCurvePointAddition, nQubits);
        }
    }
    
    ///////////////// CLASSICAL ELLIPTIC CURVE POINT ADDITION /////////////////
    ///
    /// # Summary
    /// Adds a fixed, classical elliptic curve point to
    /// a quantum point, replacing the value in the 
    /// quantum registers.
    ///
    /// # Inputs
    /// ## point1
    /// The classical point.
    /// ## point2
    /// The quantum point which will be replaced with the sum.
    ///
    /// # Operations
    /// This can test:
    ///		* DistinctEllipticCurveClassicalPointAddition
    operation EllipticCurveDistinctClassicalPointAdditionTestHelper (PointAdder : ((ECPointClassical, ECPointMontgomeryForm)=>Unit is Ctl), point1 : ECPointClassical, point2 : ECPointClassical, nQubits : Int) : Unit {
      body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits]) {

                //Write to qubit register
                mutable qpoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);

                // Rn test
                PointAdder(point1, qpoint);
 
                // Compute expected classical result
                let expected = AddClassicalECPoint(point1, point2, 0L);

                //Check results
                mutable actual = MeasureECPoint(qpoint);
                Fact(expected::x == actual::x and expected::y == actual::y and expected::z == actual::z, $"Output : Expected {expected!}, got {actual!}");

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit register
                        set qpoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled PointAdder) (controls, (point1, qpoint));

                        // Check results
                        set actual = MeasureECPoint(qpoint);
                        Fact(point2::x == actual::x and point2::y == actual::y and point2::z == actual::z, $"Control 0 : Output : Expected {point2!}, got {actual!}");

                        // Write to qubit reigster
                        set qpoint =ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled PointAdder) (controls, (point1, qpoint));

                        // Check results
                        set actual = MeasureECPoint(qpoint);
                        Fact(expected::x == actual::x and expected::y == actual::y and expected::z == actual::z, $"Control 1 : Output : Expected {expected!}, got {actual!}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }


    operation EllipticCurveDistinctClassicalPointAdditionExhaustiveTestHelper ( PointAdder : ( (ECPointClassical, ECPointMontgomeryForm) => Unit is Ctl), nQubits : Int ) : Unit {
        body (...) {
            //Nearly exhaustive list of up to 13-bit primes
            let primes = [
                [0], 
                [2, 3], 
                [5, 7], 
                [11, 13], 
                [17, 19, 23, 29, 31], 
                [37, 41, 43, 47, 53, 59, 61], 
                [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127], 
                [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251], 
                [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509], 
                [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021], 
                [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039], 
                [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093], 
                [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919]
            ];
            Fact(nQubits<=Length(primes), $"The helper does not have {nQubits}-bit primes");
            for (modulus in primes[nQubits-1]) {
                if (modulus % 4 == 3){//necessary for lazy point validation
                    for( curveround in 0 .. modulus - 1 ) {
                        //pick random elliptic curves
                        let ca = DrawRandomInt(0, modulus - 1);
                        let cb = DrawRandomInt(0, modulus - 1);
                        if ((4 * ca^3+27 * cb^2) % modulus != 0) {
                            for (pointround in 0 .. modulus - 1){
                                //pick several points on the curve to test
                                 let p1x = DrawRandomInt(0, modulus - 1);
                                 let p1signint = DrawRandomInt(0, 1);
                                 mutable p1signbool = false;
                                 if (p1signint == 1){
                                     set p1signbool = true;
                                 }
                                let cPoint1 = GetECPoint(IntAsBigInt(p1x), IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus), p1signbool);
                                let p2x = DrawRandomInt(0, modulus - 1);
                                let p2signint = DrawRandomInt(0, 1);
                                mutable p2signbool = false;
                                if (p2signint == 1){
                                    set p2signbool = true;
                                }
                                let cPoint2 = GetECPoint(IntAsBigInt(p2x), IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus), p2signbool);
                                let cPoint3 = AddClassicalECPoint(cPoint1, cPoint2, IntAsBigInt(ca));
                                //This checks for exceptional cases : 
                                //1) Where p2x is not on the curve, so cPoint2 is the identity
                                //2) Where cPoint1=cPoint2 or cPoint1=-cpoint 2
                                //3) Where cpoint+cPoint2 = -cPoint1
                                if (cPoint2::z and cPoint1::x != cPoint2::x and cPoint3::x != cPoint1::x){
                                    EllipticCurveDistinctClassicalPointAdditionTestHelper(PointAdder, cPoint1, cPoint2, nQubits);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    operation EllipticCurveDistinctClassicalPointAdditionTest () : Unit {
        body (...) {
            let nQubits = 4;
            let modulus = 13L;
            let ca = 1L;
            let cb = 7L;
            let cPoint1 = ECPointClassical(1L, 3L, true, modulus);
            let cPoint2 = ECPointClassical(2L, 11L, true, modulus);
            EllipticCurveDistinctClassicalPointAdditionTestHelper(DistinctEllipticCurveClassicalPointAddition, cPoint1, cPoint2, nQubits);
        }
    }

    operation EllipticCurveDistinctClassicalPointAdditionExhaustiveTestReversible() : Unit {
        body(...){
            let nQubits = 6;
            EllipticCurveDistinctClassicalPointAdditionExhaustiveTestHelper(DistinctEllipticCurveClassicalPointAddition, nQubits);
        }
    }

    operation EllipticCurveDistinctClassicalPointAdditionTestReversible () : Unit {
        body (...) {
            let nQubits = 256;
            let modulus = 85265314949731171755346682494076214412888213251526230821935181715916839476527L;
            let ca =      80593301813602511130620631374273968047681410450210928684196039628967115193521L;
            let cb =      12371697043807589176570267047475771490593916620347448304882995472341863115103L;
            let cPoint1 = ECPointClassical(
                83193613008967766032835933797125497968968965563238235845454568006693852956453L, 
                8819244271738210699258853614517854169335000477155860959172450199448305528798L, 
                true, modulus);
            let cPoint2 = ECPointClassical(
                45409420082015561916992843320827250888726798225855202417728324279134105369499L, 
                19471457802187571303061604600485729603048897823401976246727026320153013008395L, 
                true, modulus);
            EllipticCurveDistinctClassicalPointAdditionTestHelper(DistinctEllipticCurveClassicalPointAddition, cPoint1, cPoint2, nQubits);
        }
    }


///////////////// WINDOWED ELLIPTIC CURVE POINT ADDITION /////////////////
    ///
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
    /// # Operations
    /// This can test:
    ///		* WindowedEllipticCurvePointAddition
    ///     * WindowedEllipticCurvePointAdditionLowWidth
   operation EllipticCurveWindowedPointAdditionTestHelper (
        WindowedAdder : ((ECPointClassical[], LittleEndian, ECPointMontgomeryForm)=>Unit is Ctl), 
        inputPoints : ECPointClassical[], 
        point2 : ECPointClassical,
        address : Int, 
        addressSize : Int,
        nQubits : Int) : Unit {
      body (...) {
        // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits + addressSize]) {
                // Write to qubit registers
                mutable qPoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);
                mutable qAddress = LittleEndian(register[2* nQubits .. 2 * nQubits + addressSize - 1]);
                ApplyXorInPlaceL(IntAsBigInt(address), qAddress);
                //Run test
                WindowedAdder(inputPoints, qAddress, qPoint);
                // Compute expectd classical result
                let expected = AddClassicalECPoint(inputPoints[address], point2, 0L);
             //   let expected = ECPointClassical(0L, 0L, false, 13L);
                // Check results
                mutable actualPoint = MeasureECPoint(qPoint);
                Fact(
                    expected::x == actualPoint::x 
                    and expected::y == actualPoint::y 
                    and expected::z == actualPoint::z, 
                    $"Output : Expected {expected!}, got {actualPoint!}"
                );
                mutable actualAddress = MeasureBigInteger(qAddress);
                Fact(IntAsBigInt(address) == actualAddress, $"Output : Expected {address}, got {actualAddress}");
                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        //Write to qubit registers
                        set qPoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);
                        ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled WindowedAdder) (controls, (inputPoints, qAddress, qPoint));

                        //Check results
                        set actualPoint = MeasureECPoint(qPoint);
                        Fact(
                            point2::x == actualPoint::x 
                            and point2::y == actualPoint::y 
                            and point2::z == actualPoint::z, 
                            $"Control 0: Output : Expected {point2}, got {actualPoint!}"
                        );
                        set actualAddress = MeasureBigInteger(qAddress);
                        Fact(IntAsBigInt(address) == actualAddress, $"Control 0: Output : Expected {address}, got {actualAddress}");

                        // Write to qubit registers
                        set qPoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);
                        ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled WindowedAdder) (controls, (inputPoints, qAddress, qPoint));

                        // Check results
                        set actualPoint = MeasureECPoint(qPoint);
                        Fact(
                            expected::x == actualPoint::x 
                            and expected::y == actualPoint::y 
                            and expected::z == actualPoint::z, 
                            $"Control 1: Output : Expected {expected!}, got {actualPoint!}"
                        );
                        set actualAddress = MeasureBigInteger(qAddress);
                        Fact(IntAsBigInt(address) == actualAddress, $"Control 1: Output : Expected {address}, got {actualAddress}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation EllipticCurveWindowedPointAdditionRandomTestHelper ( 
        WindowedPointAdder : ( (ECPointClassical[], LittleEndian, ECPointMontgomeryForm) => Unit is Ctl), 
        addressSize : Int, 
        nQubits : Int,
        nTests : Int
    ) : Unit {
        body (...) {
            //Nearly exhaustive list of up to 13-bit primes
            let primes = [
                [0], 
                [2, 3], 
                [5, 7], 
                [11, 13], 
                [17, 19, 23, 29, 31], 
                [37, 41, 43, 47, 53, 59, 61], 
                [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127], 
                [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251], 
                [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509], 
                [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021], 
                [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039], 
                [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093], 
                [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919]
            ];
            Fact(nQubits<=Length(primes), $"The helper does not have {nQubits}-bit primes");
            let nPrimes = Length(primes[nQubits  - 1]);
            mutable testedIdentity = false;
            for (idxTest in 0 .. nTests - 1){
                mutable success = false;
                repeat {
                    let modulus = primes[nQubits - 1][DrawRandomInt(0, nPrimes - 1)]; 
                    if (modulus % 4 == 3){//necessary for lazy point validation
                        //pick random elliptic curves
                        let ca = DrawRandomInt(0, modulus - 1);
                        let cb = DrawRandomInt(0, modulus - 1);
                        if ((4 * ca^3 + 27 * cb^2) % modulus != 0) {
                            //pick several points on the curve to test
                            mutable cPoint1 = ECPointClassical(0L, 0L, false, IntAsBigInt(modulus));
                            if (testedIdentity){//first test should always be the identity
                                set cPoint1 = RandomNonInfinityECPoint(IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus));
                            } 
                            let cPoint2 = RandomNonInfinityECPoint(IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus));
                            let cPoint3 = AddClassicalECPoint(cPoint1, cPoint2, IntAsBigInt(ca));
                            //This checks for exceptional cases : 
                            //1) Where p2x is not on the curve, so cPoint2 is the identity
                            //2) Where cPoint1=cPoint2 or cPoint1=-cpoint 2
                            //3) Where cpoint+cPoint2 = -cPoint1
                            if (cPoint2::z and cPoint1::x != cPoint2::x and cPoint3::x != cPoint1::x){
                                let address = DrawRandomInt(0, 2 ^ addressSize - 1);
                                mutable points = new ECPointClassical[2^addressSize];
                                set points w/= address <- cPoint1;
                                EllipticCurveWindowedPointAdditionTestHelper(WindowedPointAdder, points, cPoint2, address, addressSize, nQubits);
                                set success = true;
                                if (not testedIdentity){set testedIdentity = true;} //it has tested the identity
                            }
                        }
                    }
                } until (success);
            }
        }
    }

    operation EllipticCurveWindowedPointAdditionRandomReversibleTest() : Unit {
        body(...){
            let nQubits = 6;
            let addressSize = 3;
            let nTests = 1000;
            EllipticCurveWindowedPointAdditionRandomTestHelper(WindowedEllipticCurvePointAdditionLowWidth, addressSize, nQubits, nTests);
        }
    }

    operation SignedEllipticCurveWindowedPointAdditionTestHelper (
        SignedWindowedAdder : ((ECPointClassical[], Qubit[], ECPointMontgomeryForm)=>Unit is Ctl), 
        inputPoints : ECPointClassical[], 
        point2 : ECPointClassical,
        curve : ECCurveWeierstrassClassical,
        address : Int, 
        addressSize : Int,
        nQubits : Int) : Unit {
      body (...) {
        // Bookkeeping and qubit allocation
            using (register = Qubit[2 * nQubits + addressSize]) {
                let modulus = point2::modulus;

                // Compute expected classical value
                // We expect to add (b - 2^(k-1))P where
                // P is the generator, b is the address, k
                // is the window size
                let generator = inputPoints[1];
                // Compute bP
                let addedPoint = MultiplyClassicalECPoint(generator, curve, IntAsBigInt(address));
                // Create -2^(k-1)P
                let offset = MultiplyClassicalECPoint(generator, curve, 2L^(addressSize - 1));
                let negatedOffset = ECPointClassical(offset::x, (modulus - offset::y) % modulus, offset::z, offset::modulus);
                // Add to the input point
                let expected = AddClassicalECPoint(point2, AddClassicalECPoint(addedPoint, negatedOffset, curve::a), curve::a);

                // Write to qubit registers
                mutable qPoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);
                mutable qAddress = LittleEndian(register[2* nQubits .. 2 * nQubits + addressSize - 1]);
                ApplyXorInPlaceL(IntAsBigInt(address), qAddress);
                
                //Run test
                SignedWindowedAdder(inputPoints, qAddress!, qPoint);
                // Check results
                mutable actualPoint = MeasureECPoint(qPoint);
                Fact(
                    expected::x == actualPoint::x 
                    and expected::y == actualPoint::y 
                    and expected::z == actualPoint::z, 
                    $"Output : Expected {expected!}, got {actualPoint!}"
                );
                mutable actualAddress = MeasureBigInteger(qAddress);
                Fact(IntAsBigInt(address) == actualAddress, $"Output : Expected {address}, got {actualAddress}");
                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        //Write to qubit registers
                        set qPoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);
                        ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled SignedWindowedAdder) (controls, (inputPoints, qAddress!, qPoint));

                        //Check results
                        set actualPoint = MeasureECPoint(qPoint);
                        Fact(
                            point2::x == actualPoint::x 
                            and point2::y == actualPoint::y 
                            and point2::z == actualPoint::z, 
                            $"Control 0: Output : Expected {point2}, got {actualPoint!}"
                        );
                        set actualAddress = MeasureBigInteger(qAddress);
                        Fact(IntAsBigInt(address) == actualAddress, $"Control 0: Output : Expected {address}, got {actualAddress}");
                        // Write to qubit registers
                        set qPoint = ClassicalECPointToQuantum(point2, register[0..2 * nQubits-1]);
                        ApplyXorInPlaceL(IntAsBigInt(address), qAddress);

                        // now controls are set to |1>, addition is computed
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled SignedWindowedAdder) (controls, (inputPoints, qAddress!, qPoint));

                        // Check results
                        set actualPoint = MeasureECPoint(qPoint);
                        Fact(
                            expected::x == actualPoint::x 
                            and expected::y == actualPoint::y 
                            and expected::z == actualPoint::z, 
                            $"Control 1: Output : Expected {expected!}, got {actualPoint!}"
                        );
                        set actualAddress = MeasureBigInteger(qAddress);
                        Fact(IntAsBigInt(address) == actualAddress, $"Control 1: Output : Expected {address}, got {actualAddress}");
                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation SignedEllipticCurveWindowedPointAdditionRandomTestHelper ( 
        SignedWindowedPointAdder : ( (ECPointClassical[], Qubit[], ECPointMontgomeryForm) => Unit is Ctl), 
        addressSize : Int, 
        nQubits : Int,
        nTests : Int
    ) : Unit {
        body (...) {
            //Nearly exhaustive list of up to 13-bit primes
            let primes = [
                [0], 
                [2, 3], 
                [5, 7], 
                [11, 13], 
                [17, 19, 23, 29, 31], 
                [37, 41, 43, 47, 53, 59, 61], 
                [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127], 
                [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251], 
                [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509], 
                [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021], 
                [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039], 
                [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093], 
                [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919]
            ];
            Fact(nQubits<=Length(primes), $"The helper does not have {nQubits}-bit primes");
            let nPrimes = Length(primes[nQubits  - 1]);
            for (idxTest in 0 .. nTests - 1){
                mutable success = false;
                repeat {
                    let modulus = primes[nQubits - 1][DrawRandomInt(0, nPrimes - 1)]; 
                    if (modulus % 4 == 3){//necessary for lazy point validation
                        //pick random elliptic curves
                        let bigModulus = IntAsBigInt(modulus);
                        let ca = DrawRandomInt(0, modulus - 1);
                        let cb = DrawRandomInt(0, modulus - 1);
                        if ((4 * ca^3 + 27 * cb^2) % modulus != 0) {
                            //pick several points on the curve to test
                            let curve = ECCurveWeierstrassClassical(IntAsBigInt(ca), IntAsBigInt(cb), IntAsBigInt(modulus));
                            let cPoint1 = RandomNonInfinityECPoint(IntAsBigInt(ca), IntAsBigInt(cb), bigModulus);
                            let cPoint2 = RandomNonInfinityECPoint(IntAsBigInt(ca), IntAsBigInt(cb), bigModulus);
                            let identity = ECPointClassical(0L, 0L, false, bigModulus);
                            let points = [identity] + PointTable(cPoint1, cPoint1, curve, addressSize - 1);
                            //This checks for exceptional cases : 
                            //1) Where p2x is not on the curve, so cPoint2 is the identity
                            //2) Where cPoint1=cPoint2 or cPoint1=-cpoint 2
                            //3) Where cpoint+cPoint2 = -cPoint1
                            let address = DrawRandomInt(0, 2 ^ addressSize - 1);
                            mutable tablePoint = points[address % 2^(addressSize - 1)];
                            if ((address / 2^(addressSize - 1)) == 0){
                                set tablePoint = points[2^(addressSize - 1) - address];
                                set tablePoint = ECPointClassical(
                                    tablePoint::x,
                                    (bigModulus - tablePoint::y) % bigModulus,
                                    tablePoint::z,
                                    bigModulus
                                );
                            }
                            let cPoint3 = AddClassicalECPoint(cPoint2, tablePoint, IntAsBigInt(ca));
                            if (cPoint2::z and tablePoint::z and tablePoint::x != cPoint2::x and cPoint3::x != tablePoint::x){
                                Message($"Running test {idxTest} on curve {ca},{cb}");
                                SignedEllipticCurveWindowedPointAdditionTestHelper(
                                    SignedWindowedPointAdder, 
                                    points, 
                                    cPoint2, 
                                    curve,
                                    address, 
                                    addressSize, 
                                    nQubits
                                );
                                set success = true;
                            }
                        }
                    }
                } until (success);
            }
        }
    }

    operation SignedEllipticCurveWindowedPointAdditionRandomReversibleTest() : Unit {
        body(...){
            let nQubits = 6;
            let addressSize = 3;
            let nTests = 1000;
            SignedEllipticCurveWindowedPointAdditionRandomTestHelper(SignedWindowedEllipticCurvePointAdditionLowWidth, addressSize, nQubits, nTests);
        }
    }

    operation ShorAdditionTestHelper(
        PointAdder : ( (ECPointClassical, ECPointMontgomeryForm) => Unit is Ctl),
        curve : ECCurveWeierstrassClassical, 
        generator : ECPointClassical,
        curveOrder : BigInt,
        nTests : Int
    ) : Unit {
        //idea: pick random point, add all doubled multiples of that point, and all doubled multiples of P
        let nBits = BitSizeL(curve::modulus);
        for (idxTest in 0 .. nTests - 1){
            Message($"    Running test {idxTest} of {nTests}");
            let Q1 = MultiplyClassicalECPoint(generator, curve, RandomBigInt(curveOrder-1L)+1L);
            let Q2 = MultiplyClassicalECPoint(generator, curve, RandomBigInt(curveOrder-1L)+1L);
            EllipticCurveDistinctClassicalPointAdditionTestHelper (PointAdder, Q1, Q2, nBits);
        }
    }

    operation TestShor() : Unit {
        let nTests = 10;
        let pointAdder = DistinctEllipticCurveClassicalPointAddition;
        let curves = [
            ThirtyBitCurve,
            NISTP192,
            NISTP224,
            NISTP256,
            NISTP384,
            NISTP521,
            Secp256k1,
            Curve25519
        ];
        for (curveFunction in curves){
            let (curve, generator, curveOrder, name) = curveFunction();
            Message("Testing curve: " + name);
            ShorAdditionTestHelper(
                pointAdder,
                curve, 
                generator,
                curveOrder,
                nTests
            );
            Message("Test passed.");
        }
    }

    // Picks random points, but exhaustively checks all addresses
    // within the specified window size.
    operation ShorAdditionWindowedExhaustiveTestHelper ( 
        SignedWindowedPointAdder : ( (ECPointClassical[], Qubit[], ECPointMontgomeryForm) => Unit is Ctl), 
        curve : ECCurveWeierstrassClassical, 
        generator : ECPointClassical,
        curveOrder : BigInt,
        windowSize : Int
    ) : Unit {
        let nQubits = BitSizeL(curve::modulus);
        let startWindow = DrawRandomInt(0, nQubits - 1);
        let startPoint = MultiplyClassicalECPoint(generator, curve, 2L^startWindow);
        let identity = ECPointClassical(0L, 0L, false, curve::modulus);
        let points = [identity] + PointTable(startPoint, startPoint, curve, windowSize - 1);
        let Q = MultiplyClassicalECPoint(generator, curve, RandomBigInt(curveOrder-1L)+1L);
        Message("    Test prepped, about to run");
        for (address in 0 .. 2^windowSize -1){
            Message($"Address: {address}");
            SignedEllipticCurveWindowedPointAdditionTestHelper(
                SignedWindowedPointAdder, 
                points, 
                Q, 	
                curve,
                address, 
                windowSize, 
                nQubits
            );
        }
    }


    // Picks random points, but exhaustively checks all addresses
    // within the specified window size.
    operation ExhaustiveTestSignedWindowedShor() : Unit {
        let windowSize = 4;
        let pointAdder = SignedWindowedEllipticCurvePointAdditionLowWidth;
        let curves = [
            TenBitCurve,
            ThirtyBitCurve,
            NISTP192,
            NISTP224,
            NISTP256,
            NISTP384,
            NISTP521,
            Secp256k1,
            Curve25519
        ];
        for (curveFunction in curves){
            let (curve, generator, curveOrder, name) = curveFunction();
            Message("Testing curve: " + name);
            ShorAdditionWindowedExhaustiveTestHelper(
                pointAdder,
                curve, 
                generator,
                curveOrder,
                windowSize
            );
            Message("Test passed.");
        }
    }

     operation ShorAdditionWindowedRandomTestHelper ( 
        SignedWindowedPointAdder : ( (ECPointClassical[], Qubit[], ECPointMontgomeryForm) => Unit is Ctl), 
        curve : ECCurveWeierstrassClassical, 
        generator : ECPointClassical,
        curveOrder : BigInt,
        nTests : Int
    ) : Unit {
        let nQubits = BitSizeL(curve::modulus);
        let windowSize = OptimalSignedPointAdditionWindowSize(nQubits);
        Message($"Window size: {windowSize}");
        
        for (idxTest in 0 .. nTests - 1){
            Message($"    Prepping test {idxTest} of {nTests}");
            let startWindow = DrawRandomInt(0, nQubits - 1);
            let startPoint = MultiplyClassicalECPoint(generator, curve, 2L^startWindow);
            let address = DrawRandomInt(0, 2 ^ windowSize - 1);
            let identity = ECPointClassical(0L, 0L, false, curve::modulus);
            let points = [identity] + PointTable(startPoint, startPoint, curve, windowSize - 1);

            let Q = MultiplyClassicalECPoint(generator, curve, RandomBigInt(curveOrder-1L)+1L);
            Message("    Test prepped, about to run");
            SignedEllipticCurveWindowedPointAdditionTestHelper(
                SignedWindowedPointAdder, 
                points, 
                Q, 	
                curve,
                address, 
                windowSize, 
                nQubits
            );
        }
    }

    // Picks random points and random addresses
    operation RandomTestSignedWindowedShor() : Unit {
        let nTests = 10;
        let pointAdder = SignedWindowedEllipticCurvePointAdditionLowWidth;
        let curves = [
            TenBitCurve,
            ThirtyBitCurve,
            NISTP192,
            NISTP224,
            NISTP256,
            NISTP384,
            NISTP521,
            Secp256k1,
            Curve25519
        ];
        for (curveFunction in curves){
            let (curve, generator, curveOrder, name) = curveFunction();
            Message("Testing curve: " + name);
            ShorAdditionWindowedRandomTestHelper(
                pointAdder,
                curve, 
                generator,
                curveOrder,
                nTests
            );
            Message("Test passed.");
        }
    }

}