namespace Quantum.ModularAddition
{
    using cs;
    using Microsoft.Quantum.Crypto.Canon;
    using Microsoft.Quantum.Simulation.Simulators;
    using Microsoft.Quantum.Simulation.Simulators.QCTraceSimulators;
    using ModularArithmeticTimingTests;
    using System;
    using System.Collections.Generic;
    using System.Threading;

    class Driver
    {
        public delegate System.Threading.Tasks.Task<Microsoft.Quantum.Simulation.Core.QVoid> RunQop(QCTraceSimulator sim, long n, bool isControlled);
        public delegate System.Threading.Tasks.Task<Microsoft.Quantum.Simulation.Core.QVoid> RunParameterizedQop(QCTraceSimulator sim, long n, bool isControlled, long m);

        public static void Main(string[] args)
        {
            var subFolder = "LowDepth/"; // <- Change when running alternate optimization strategies

            int[] bigTestSizes = {4, 8, 16, 32, 64, 110, 128, 160, 192, 224, 256, 384, 512};
            int[] smallSizes = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25};
            int[] ellipticCurveTestSizes = {110, 160, 192, 224, 256, 384, 521};
            int[] fixedEllipticCurveTestSizes = {10, 30, 192, 224, 256, 384, 521};

            // construct list of bit sizes
            List<int> exhaustiveArithmeticSizes = new List<int>();
            List<int> exhaustiveSmallCurveSizes = new List<int>();
            System.Random rnd = new System.Random();
            for (int i = 4; i < 64; i ++) {
                exhaustiveArithmeticSizes.Add(i);
                exhaustiveSmallCurveSizes.Add(i);
            }
            // Checking all bit sizes between 64 and 2048 would be too many
            // Incrementing by a fixed value might cause issues with regularities
            // in Hamming weight, etc.; choosing random increments avoids this.
            for (int i = 64; i <= 2048; i += 8 + rnd.Next(5)) {
                exhaustiveArithmeticSizes.Add(i);
            }
            exhaustiveSmallCurveSizes.AddRange(ellipticCurveTestSizes);


            EstimateModularMultiplicationWindowSizes(bigTestSizes, "ModularMultiplicationWindows/" + subFolder, 0);

            EstimateCheapModularArithmetic(exhaustiveArithmeticSizes.ToArray(), "ModularArithmeticEstimates/" + subFolder);
            EstimateExpensiveModularArithmetic(exhaustiveSmallCurveSizes.ToArray(), "ModularArithmeticEstimates/" + subFolder);
            EstimateArithmetic(exhaustiveArithmeticSizes.ToArray(), "ArithmeticEstimates/" + subFolder);
            EstimatePointLookups(ellipticCurveTestSizes, "LookupEstimates/" + subFolder);
            EstimateEllipticCurveArithmetic(exhaustiveSmallCurveSizes.ToArray(), "EllipticCurveEstimates/" + subFolder);
            EstimateFixedEllipticCurveArithmetic(fixedEllipticCurveTestSizes, "EllipticCurveEstimates/" + subFolder);
        }

        public static void EstimateLookup(int[] testSizes, string directory) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                for (int i = 0; i < 2; i++) {
                    var localControl = isControlled;
                    var localGates = allGates;
                    Thread lookupThread = new Thread(() => BasicResourceTest<LookUpTimingTest>(LookUpTimingTest.Run, testSizes, localControl,
                        directory + "Lookup", localGates, true));
                    lookupThread.Start();
                    isControlled = !isControlled;
                }
                allGates = !allGates;
            }
        }

        public static void EstimateArithmetic(int[] testSizes, string directory) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                for (int i = 0; i < 2; i++) {
                    //Creates a new thread for each operation being estimated
                    var localControl = isControlled;
                    var localGates = allGates;
                    // Thread onesThread = new Thread(() => BasicResourceTest<TestifAllOneTimingTest>(TestifAllOneTimingTest.Run, testSizes, localControl,
                    //       directory + "AllOnes", localGates, false));
                    // onesThread.Start();
                    Thread additionThread = new Thread(() => BasicResourceTest<AdditionTimingTest>(AdditionTimingTest.Run, testSizes, localControl,
                          directory + "Addition", localGates, false));
                    additionThread.Start();
                    // Thread additionNoCarryThread = new Thread(() => BasicResourceTest<AdditionTimingTestNoCarry>(AdditionTimingTestNoCarry.Run, testSizes, localControl,
                    //      directory + "Addition-no-carry", localGates, false));
                    // additionNoCarryThread.Start();
                    // Thread constantAdditionThread = new Thread(() => BasicResourceTest<ConstantAdditionTimingTest>(ConstantAdditionTimingTest.Run, testSizes, localControl,
                    //     directory + "Constant-addition", localGates, false));
                    // constantAdditionThread.Start();
                    Thread greaterThanThread = new Thread(() => BasicResourceTest<GreaterThanTimingTest>(GreaterThanTimingTest.Run, testSizes, localControl,
                        directory + "Greater-than", localGates, false));
                    greaterThanThread.Start();
                    isControlled = !isControlled;
                }
                allGates = !allGates;
            }
        }

        // Estimates how large an optimal window should be, by iterating through
        // all possible window sizes and checking total cost.
        // This is an extremely costly estimate to run.
        public static void EstimatePointAdditionWindowSizes(int[] testSizes, string directory, int costMetric) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            //Guesses
            int[] minWindowSizes = {14,  15,  15,  15,  16,  16,  16};
            int[] maxWindowSizes ={18,  18,  18,  18,  20,  20,  20};

            System.IO.Directory.CreateDirectory(directory);

            bool allGates = false;
            bool isControlled = false;

            var localControl = isControlled;
            var localGates = allGates;
            Thread lowWidthThread = new Thread(() => ParameterizedResourceTest<EllipticCurveWindowedPointAdditionLowWidthWindowTest>(
                EllipticCurveWindowedPointAdditionLowWidthWindowTest.Run, testSizes, localControl, true, true, //costMetric,
                directory + "Point-addition-windowed-low-width", localGates,
                minWindowSizes, maxWindowSizes));
            lowWidthThread.Start();
            Thread highWidthThread = new Thread(() => ParameterizedResourceTest<EllipticCurveWindowedPointAdditionWindowTest>(
                EllipticCurveWindowedPointAdditionWindowTest.Run, testSizes, localControl, true, true, //costMetric,
                directory + "Point-addition-windowed", localGates,
                minWindowSizes, maxWindowSizes));
            highWidthThread.Start();
            Thread signedThread = new Thread(() => ParameterizedResourceTest<EllipticCurveSignedWindowedPointAdditionWindowTest>(
                EllipticCurveSignedWindowedPointAdditionWindowTest.Run, testSizes, localControl, true, true, //costMetric,
                directory + "Point-addition-windowed-signed", localGates,
                minWindowSizes, maxWindowSizes));
            signedThread.Start();
        }

        // Estimates cost to look up points for a number of window sizes
        // if the points have a specific bitlength.
        public static void EstimatePointLookups(int[] testSizes, string directory) {
            var maxWindowSize = 10;


            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            //Construct window size maximum and minimum values
            // Idea: Minimum value is 1, maximum value is the full
            // size, or a value which is too large to reasonably simulate
            int[] minWindowSizes = new int[testSizes.Length];
            int[] maxWindowSizes = new int[testSizes.Length];
            for (int i = 0; i < testSizes.Length; i++) {
                minWindowSizes[i] = 1;
                maxWindowSizes[i] = Math.Min(testSizes[i], maxWindowSize); //2^23 should take about 2 hours
            }


            System.IO.Directory.CreateDirectory(directory);

            //Loops over whether it counts all all-gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                //Creates a new thread for each operation being estimated
                var localControl = isControlled;
                var localGates = allGates;
                Thread lookupThread = new Thread(() => ParameterizedResourceTest<PointLookUpTimingTest>(
                    PointLookUpTimingTest.Run, testSizes, localControl, false, true, //costMetric,
                    directory + "Point-lookup", localGates,
                    minWindowSizes, maxWindowSizes));
                lookupThread.Start();

                allGates = !allGates;
            }
        }

        // Estimates window sizes for modular arithmetic
        // See ReadMe
        public static void EstimateModularMultiplicationWindowSizes(int[] testSizes, string directory, int costMetric) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            //Construct window size maximum and minimum values
            // Idea: Minimum value is 0 (no windowing), maximum value is the full
            // size, or a value which is too large to reasonably simulate
            int[] minWindowSizes = new int[testSizes.Length];
            int[] maxWindowSizes = new int[testSizes.Length];
            for (int i = 0; i < testSizes.Length; i++) {
                minWindowSizes[i] = 0;
                maxWindowSizes[i] = Math.Min(testSizes[i], 23); //2^23 should take about 2 hours
            }

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                for (int i = 0; i < 2; i++) {
                    var localControl = isControlled;
                    var localGates = allGates;
                    Thread multiplyThread = new Thread(() => ParameterizedResourceTestSingleThreaded<MontgomeryWindowedMultiplicationWindowTest>(
                        MontgomeryWindowedMultiplicationWindowTest.Run, testSizes, localControl, false, costMetric,
                        directory + "Modular-multiplication-windowed", localGates,
                        minWindowSizes, maxWindowSizes));
                    multiplyThread.Start();
                    isControlled = !isControlled;
                }
                allGates = !allGates;
            }
        }

        // Estimates modular addition-like operations, which can be reasonable
        // estimated for bit sizes over 500
        public static void EstimateCheapModularArithmetic(int[] testSizes, string directory) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                for (int i = 0; i < 2; i++) {
                     var localControl = isControlled;
                     var localGates = allGates;
                    Thread doubleThread = new Thread(() => BasicResourceTest<ModularDblTimingTest>(ModularDblTimingTest.Run, testSizes, localControl,
                        directory + "Modular-double", localGates, false));
                    doubleThread.Start();
                    Thread additionThread = new Thread(() => BasicResourceTest<ModularAdditionTimingTest>(ModularAdditionTimingTest.Run, testSizes, localControl,
                        directory + "Modular-addition", localGates, false));
                    additionThread.Start();
                    isControlled = !isControlled;
                }
                allGates = !allGates;
            }
        }

        // "Expensive" modular operations, including square, multiplication, inversion
        // Does not check controlled vs. not controlled because the extra cost is so small,
        // and the operations are so costly to estimate.
        public static void EstimateExpensiveModularArithmetic(int[] testSizes, string directory) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                  var localControl = isControlled;
                 var localGates = allGates;
                Thread multiplyThread = new Thread(() => BasicResourceTest<MontgomeryMultiplicationTimingTest>(MontgomeryMultiplicationTimingTest.Run, testSizes, localControl,
                    directory + "Modular-multiplication", localGates, true));
                multiplyThread.Start();

                // This is run as a comparison to the windowed version
                Thread multipyNoWindowsThread = new Thread(() => BasicResourceTest<NonWindowedMontgomeryMultiplicationTimingTest>(NonWindowedMontgomeryMultiplicationTimingTest.Run, testSizes, localControl,
                    directory + "Modular-multiplication-no-windows", localGates, true));
                 multipyNoWindowsThread.Start();

                Thread squareThread = new Thread(() => BasicResourceTest<MontgomerySquareTimingTest>(MontgomerySquareTimingTest.Run, testSizes, localControl,
                    directory + "Modular-squaring", localGates, true));
                squareThread.Start();
                Thread invertThread = new Thread(() => BasicResourceTest<MontgomeryInversionTimingTest>(MontgomeryInversionTimingTest.Run, testSizes, localControl,
                    directory + "Modular-Inversion", localGates, true));
                invertThread.Start();
                Thread divideThread = new Thread(() => BasicResourceTest<ModularDivisionTimingTest>(ModularDivisionTimingTest.Run, testSizes, localControl,
                    directory + "Modular-division", localGates, true));
                divideThread.Start();
                allGates = !allGates;
            }
        }

        // Checks only signed, windowed point addition.
        // Others could be enabled
        public static void EstimateEllipticCurveArithmetic(int[] testSizes, string directory) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                var localControl = isControlled;
                var localGates = allGates;
                // Constant point addition is controlled, the others are not,
                // because in Shor's algorithm they do not need to be.
                // Thread nonWindowedThread = new Thread(() => BasicResourceTest<EllipticCurveConstantPointAdditionTimingTest>(EllipticCurveConstantPointAdditionTimingTest.Run, testSizes, true,
                //     directory + "Constant-point-addition", localGates, true));
                // nonWindowedThread.Start();
                // // Thread windowedThread = new Thread(() => BasicResourceTest<EllipticCurveWindowedPointAdditionTimingTest>(EllipticCurveWindowedPointAdditionTimingTest.Run, testSizes, false,
                // //     directory + "Windowed-point-addition", localGates, true));
                // // windowedThread.Start();
                // // Thread lowWidthThread = new Thread(() => BasicResourceTest<EllipticCurveWindowedPointAdditionLowWidthTimingTest>(EllipticCurveWindowedPointAdditionLowWidthTimingTest.Run, testSizes, false,
                // //     directory + "Windowed-point-addition-low-width", localGates, true));
                // // lowWidthThread.Start();
                Thread signedThread = new Thread(() => BasicResourceTest<EllipticCurveSignedWindowedPointAdditionTimingTest>(EllipticCurveSignedWindowedPointAdditionTimingTest.Run, testSizes, false,
                     directory + "Windowed-point-addition-signed", localGates, true));
                signedThread.Start();
                //  Thread fixedThread = new Thread(() => BasicResourceTest<FixedEllipticCurveSignedWindowedPointAdditionTimingTest>(FixedEllipticCurveSignedWindowedPointAdditionTimingTest.Run, testSizes, false,
                //     directory + "Fixed-modulus-signed", localGates, true));
                // fixedThread.Start();
                allGates = !allGates;
            }
        }

        // Checks only signed, windowed point addition for which there are fixed parameters.
        public static void EstimateFixedEllipticCurveArithmetic(int[] testSizes, string directory) {
            // Writes global parameters (cost metric, testable gates) to terminal
            var qsim = new ToffoliSimulator();
            OutputGlobalParameters.Run(qsim).Wait();
            qsim = null;

            System.IO.Directory.CreateDirectory(directory);

            //Loops over controlled/not and whether it counts all gates
            bool allGates = false;
            bool isControlled = false;
            for (int j = 0; j < 2; j++) {
                var localControl = isControlled;
                var localGates = allGates;
                 Thread fixedThread = new Thread(() => BasicResourceTest<FixedEllipticCurveSignedWindowedPointAdditionTimingTest>(FixedEllipticCurveSignedWindowedPointAdditionTimingTest.Run, testSizes, false,
                    directory + "Fixed-modulus-signed", localGates, true));
                fixedThread.Start();
                allGates = !allGates;
            }
        }


        /// # Summary
        /// Returns a trace simulator object that is configured
        /// to measure depth, width, and primitive operation count.
        /// If `full_depth` is true, then it counts every gate as depth 1;
        /// otherwise it only counts T gates
        static QCTraceSimulator getTraceSimulator(bool full_depth)
        {
            var config = new QCTraceSimulatorConfiguration();
            config.UseDepthCounter = true;
            config.UseWidthCounter = true;
            config.UsePrimitiveOperationsCounter = true;
            if (full_depth)
            {
                config.TraceGateTimes[PrimitiveOperationsGroups.CNOT] = 1;
                config.TraceGateTimes[PrimitiveOperationsGroups.Measure] = 1; // count all one and 2 qubit measurements as depth 1
                config.TraceGateTimes[PrimitiveOperationsGroups.QubitClifford] = 1; // qubit Clifford depth 1
            }
            return new QCTraceSimulator(config);
        }

        /// # Summary
        /// Runs a specified quantum operation with different parameters `ns`,
        /// saving the resource estimates as a csv file to a specified location.
        ///
        /// # Inputs
        /// ## runner
        /// The quantum operation being tested (must also match the type `Qop`).
        /// This operation must take a boolean `isControlled` and an integer parameter
        /// ## ns
        /// An array of integer parameters. This method will run the quantum operation
        /// with each parameter
        /// ## isControlled
        /// A boolean argument to pass to the quantum operation. The intention is that
        /// it tells the operator whether to test a controlled or uncontrolled version.
        /// ## filename
        /// The filename, including directory, of where to save the results
        /// ## full_depth
        /// If true, counts all gates as depth 1; if false, only counts T-gates as depth 1,
        /// all others as depth 0
        static void BasicResourceTest<Qop>(RunQop runner, int[] ns, bool isControlled, string filename, bool full_depth, bool isThreaded)
        {
            if (full_depth) {
                filename += "-all-gates";
            }
            if (isControlled) {
                filename += "-controlled";
            }
            filename += ".csv";
            string estimation = "";
            // Headers for the table
            if (!System.IO.File.Exists(filename)) {
                estimation += " operation, CNOT count, 1-qubit Clifford count, T count, R count, M count, ";
                if (full_depth) { estimation += "Full depth, ";}
                else {estimation += "T depth, ";}
                estimation += "initial width, extra width, comment, size";
                System.IO.File.WriteAllText(filename, estimation);
            }
            // Run the test for every size
            ReaderWriterLock locker = new ReaderWriterLock();
            for (int i = 0; i < ns.Length; i++)
            {
                if (isThreaded) {
                    var thisThreadParameter = ns[i];
                    Thread oneParameterTest = new Thread(() => SingleResourceTest<Qop>(
                        runner, locker, thisThreadParameter, isControlled, filename, full_depth));
                    oneParameterTest.Start();
                } else {
                    //Single thread
                    SingleResourceTest<Qop>(runner, locker, ns[i], isControlled, filename, full_depth);
                }
            }
        }

        static void SingleResourceTest<Qop>(RunQop runner, ReaderWriterLock locker, int n, bool isControlled, string filename, bool full_depth)
        {
            QCTraceSimulator estimator = getTraceSimulator(full_depth); //construct simulator object
            //we must generate a new simulator in each round, to clear previous estimates
            var res = runner(estimator, n, isControlled).Result; //run test
            // Create string of a row of parameters
            string thisCircuitCosts = DisplayCSV.CSV(estimator.ToCSV(), typeof(Qop).FullName, false, "", false, "");
            // add the row to the string of the csv
            thisCircuitCosts +=  $"{n}";
            try
            {
                locker.AcquireWriterLock(int.MaxValue); //absurd timeout value
                System.IO.File.AppendAllText(filename, thisCircuitCosts);
            }
            finally
            {
                locker.ReleaseWriterLock();
            }
        }

        /// # Summary
        /// Runs a specified quantum operation with different parameters `ns`,
        /// saving the resource estimates as a csv file to a specified location.
        /// This also runs the operation with a second parameter, which varies
        /// between specified minimum and maximum values. It only runs over the
        /// second parameter until it minimizes depth and T count.
        /// The main purpose is to estimate optimal window sizes for windowed operations.
        ///
        /// # Inputs
        /// ## runner
        /// The quantum operation being tested (must also match the type `Qop`).
        /// This operation must take a boolean `isControlled` and an integer parameter
        /// ## ns
        /// An array of integer parameters. This method will run the quantum operation
        /// with each parameter
        /// ## isControlled
        /// A boolean argument to pass to the quantum operation. The intention is that
        /// it tells the operator whether to test a controlled or uncontrolled version.
        /// ## isAmortized
        /// Decides how to select the optimal second parameter. If it's amortized, it divides
        /// the resulting cost by the value of the second parameter. This is intended
        /// for windowed addition: as the window size increases, we need to do fewer additions.
        /// ## filename
        /// The filename, including directory, of where to save the results
        /// ## full_depth
        /// If true, counts all gates as depth 1; if false, only counts T-gates as depth 1,
        /// all others as depth 0
        /// ## minParameters
        /// The minimum value for the second parameter, corresponding to values in ns
        /// ## maxParameters
        /// The maximum value for the second parameter.
        static void ParameterizedResourceTest<Qop>(
            RunParameterizedQop runner,
            int[] ns,
            bool isControlled,
            bool isOptimized,
            bool isAmortized,
            string filename,
            bool full_depth,
            int[] minParameters,
            int[] maxParameters)
        {
            if (full_depth) {
                filename += "-all-gates";
            }
            if (isControlled) {
                filename += "-controlled";
            }
            filename += ".csv";
            // Create table headers
            if (!System.IO.File.Exists(filename)) {
                string estimation = "";
                estimation += " operation, CNOT count, 1-qubit Clifford count, T count, R count, M count, ";
                if (full_depth) { estimation += "Full depth, ";}
                else {estimation += "T depth, ";}
                estimation += "initial width, extra width, comment, size, parameter";
                System.IO.File.WriteAllText(filename, estimation);
            }

            ReaderWriterLock locker = new ReaderWriterLock();

            for (int i = 0; i < ns.Length; i++)
            {
                // Local variables to prevent threading issues
                var thisThreadProblemSize = ns[i];
                var thisTheadMinParameter = minParameters[i];
                var thisThreadMaxParameter = maxParameters[i];
                // Starts a thread for each value in ns.
                // Each thread will independently search for an optimal size.
                if (isOptimized) {
                    Thread oneParameterTest = new Thread(() => SingleParameterizedResourceTest<Qop>(
                        runner, locker, thisThreadProblemSize, thisTheadMinParameter, thisThreadMaxParameter,
                        isControlled, filename, full_depth, isAmortized));
                    oneParameterTest.Start();
                } else {
                    for (int j = minParameters[i]; j <= maxParameters[i]; j++) {
                        var thisThreadParameter = j;
                        Thread oneParameterTest = new Thread(() => SingleResourceTestNoCost<Qop>(
                            runner, locker, thisThreadProblemSize, thisThreadParameter,
                            isControlled, filename, full_depth));
                        oneParameterTest.Start();
                    }
                }
            }
        }
        static void SingleParameterizedResourceTest<Qop>(
            RunParameterizedQop runner,
            ReaderWriterLock locker,
            int n,
            int minParameter,
            int maxParameter,
            bool isControlled,
            string filename,
            bool full_depth,
            bool isAmortized)
        {
            //Track best cost
            var bestDepth = 9223372036854775807.0;
            var bestTGates = 9223372036854775807.0;
            // Iterate through values of the second parameter
            for (int j = minParameter; j < maxParameter; j++) {
                QCTraceSimulator estimator = getTraceSimulator(full_depth); //construct simulator object
                //we must generate a new simulator in each round, to clear previous estimates
                var res = runner(estimator, n, isControlled, j).Result; //run test
                // Get results
                var roundDepth = estimator.GetMetric<Qop>(MetricsNames.DepthCounter.Depth);
                var roundTGates = estimator.GetMetric<Qop>(PrimitiveOperationsGroupsNames.T);
                // If amortized, we divide out the cost of this round
                if (isAmortized) {
                    roundDepth = roundDepth / j;
                    roundTGates = roundTGates / j;
                }

                // Create string of a row of parameters
                string thisCircuitCosts = DisplayCSV.CSV(estimator.ToCSV(), typeof(Qop).FullName, false, "", false, "");
                // add the row to the string of the csv
                thisCircuitCosts +=  $"{n}, {j}";
                try
                {
                    locker.AcquireWriterLock(int.MaxValue); //absurd timeout value
                    System.IO.File.AppendAllText(filename, thisCircuitCosts);
                }
                finally
                {
                    locker.ReleaseWriterLock();
                }
                // Breaks if it's reached the minimum in both metrics
                // Assumes the metrics are convex
                if (roundDepth >= bestDepth && roundTGates >= bestTGates) {
                    break;
                } else {
                    if (roundDepth < bestDepth) {
                        bestDepth = roundDepth;
                    }
                    if (roundTGates < bestTGates) {
                        bestTGates = roundTGates;
                    }
                }
            }
        }
        static void SingleResourceTestNoCost<Qop>(
            RunParameterizedQop runner,
            ReaderWriterLock locker,
            int n,
            int m,
            bool isControlled,
            string filename,
            bool full_depth)
        {
            QCTraceSimulator estimator = getTraceSimulator(full_depth); //construct simulator object
            //we must generate a new simulator in each round, to clear previous estimates
            var res = runner(estimator, n, isControlled, m).Result; //run test
            // Get results

            // Create string of a row of parameters
            string thisCircuitCosts = DisplayCSV.CSV(estimator.ToCSV(), typeof(Qop).FullName, false, "", false, "");
            // add the row to the string of the csv
            thisCircuitCosts +=  $"{n}, {m}";
            try
            {
                locker.AcquireWriterLock(int.MaxValue); //absurd timeout value
                System.IO.File.AppendAllText(filename, thisCircuitCosts);
            }
            finally
            {
                locker.ReleaseWriterLock();
            }
        }

        static void ParameterizedResourceTestSingleThreaded<Qop>(
            RunParameterizedQop runner,
            int[] ns,
            bool isControlled,
            bool isAmortized,
            int costMetric,
            string filename,
            bool full_depth,
            int[] minParameters,
            int[] maxParameters)
        {
            if (full_depth) {
                filename += "-all-gates";
            }
            if (isControlled) {
                filename += "-controlled";
            }
            filename += ".csv";
            // Create table headers if file does not already exist
            if (!System.IO.File.Exists(filename)) {
                string estimation = "";
                estimation += " operation, CNOT count, 1-qubit Clifford count, T count, R count, M count, ";
                if (full_depth) { estimation += "Full depth, ";}
                else {estimation += "T depth, ";}
                estimation += "initial width, extra width, comment, size, parameter";
                System.IO.File.WriteAllText(filename, estimation);
            }

            var bestParameter = minParameters[0];
            for (int i = 0; i < ns.Length; i++)
            {
                // Starts a thread for each value in ns.
                // Each thread will independently search for an optimal size.
                var bestCost = 9223372036854775807.0;
                // Iterate through values of the second parameter
                for (int j = bestParameter; j < maxParameters[i]; j++) {
                    QCTraceSimulator estimator = getTraceSimulator(full_depth); //construct simulator object
                    //we must generate a new simulator in each round, to clear previous estimates
                    var res = runner(estimator, ns[i], isControlled, j).Result; //run test
                    // Get results
                    var roundCost = 0.0;
                    if (costMetric == 0) {//depth
                        roundCost = estimator.GetMetric<Qop>(MetricsNames.DepthCounter.Depth);
                    } else {
                        roundCost = estimator.GetMetric<Qop>(PrimitiveOperationsGroupsNames.T);
                    }
                    // If amortized, we divide out the cost of this round
                    if (isAmortized) {
                        roundCost = roundCost / j;
                    }

                    // Create string of a row of parameters
                    string thisCircuitCosts = DisplayCSV.CSV(estimator.ToCSV(), typeof(Qop).FullName, false, "", false, "");
                    // add the row to the string of the csv
                    thisCircuitCosts +=  $"{ns[i]}, {j}";

                    System.IO.File.AppendAllText(filename, thisCircuitCosts);
                    // Breaks if it's reached the minimum in both metrics
                    // Assumes the metrics are convex and increasing in n
                    if (roundCost > bestCost) {
                        break;
                    } else if (roundCost < bestCost) {
                        bestCost = roundCost;
                        bestParameter = j;
                    }
                }
            }
        }
    }
}
