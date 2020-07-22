﻿using Microsoft.Quantum.Simulation.Simulators;
using Microsoft.Quantum.Simulation.XUnit;
using System.Diagnostics;
using Xunit.Abstractions;

namespace Test
{
    public class TestSuiteRunner
    {
        private readonly ITestOutputHelper output;

        public TestSuiteRunner(ITestOutputHelper output)
        {
            this.output = output;
        }

        /// <summary>
        /// This driver will run all Q# tests (operations named "...Test")
        /// that belong to namespace Test.
        ///
        /// To execute your tests, just type "dotnet test" from the command line.
        /// </summary>
        [OperationDriver(TestNamespace = "Microsoft.Quantum.Crypto.Tests")]
        public void TestTarget(TestOperation op)
        {
            var sim = new ToffoliSimulator();
            // OnLog defines action(s) performed when Q# test calls function Message
            sim.OnLog += (msg) => { output.WriteLine(msg); };
            sim.OnLog += (msg) => { Debug.WriteLine(msg); };
            op.TestOperationRunner(sim);
        }
    }
}
