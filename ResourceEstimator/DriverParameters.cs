// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Quantum.ModularAddition
{
    using System;
    using Microsoft.Quantum.Crypto.Basics;
    using Microsoft.Quantum.Simulation.Simulators;
    using Microsoft.Quantum.Simulation.Simulators.QCTraceSimulators;

    public static class DriverParameters
    {
        static DriverParameters()
        {
            var qsim = new ToffoliSimulator();

            DriverParameters.IsTestable = IsMinimizeDepthCostMetric.Run(qsim).Result;
            DriverParameters.MinimizeDepthCostMetric = IsMinimizeDepthCostMetric.Run(qsim).Result;
            DriverParameters.MinimizeTCostMetric = IsMinimizeTCostMetric.Run(qsim).Result;
            DriverParameters.MinimizeWidthCostMetric = IsMinimizeWidthCostMetric.Run(qsim).Result;
        }

        public static bool IsTestable { get; private set; }

        public static bool MinimizeDepthCostMetric { get; private set; }

        public static bool MinimizeTCostMetric { get; private set; }

        public static bool MinimizeWidthCostMetric { get; private set; }

        public static void Print()
        {
            if (IsTestable)
            {
                Console.WriteLine("Running testable functions");
            }
            else
            {
                Console.WriteLine("Running non-testable functions");
            }

            if (MinimizeDepthCostMetric)
            {
                Console.WriteLine("Minimizing depth");
            }
            else if (MinimizeTCostMetric)
            {
                Console.WriteLine("Minimizing T gates");
            }
            else
            {
                Console.WriteLine("Minimizing width");
            }
        }
    }
}