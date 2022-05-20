// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Basics
{
    using System;
    using Microsoft.Quantum.Simulation.Core;
    using Microsoft.Quantum.Simulation.QCTraceSimulatorRuntime;

    public partial class IsTestable
    {
        /// <summary>
        /// Set to true to run unit tests, false to run the resource estimator.
        /// </summary>
        public static bool Testable { set; get; } = true;

        public class Native : IsTestable
        {
            public Native(IOperationFactory m)
                : base(m)
            {
            }

            public override Func<QVoid, bool> __Body__ => IsTestableFunc;

            public static bool IsTestableFunc(QVoid qVoid)
            {
                return Testable;
            }
        }
    }
}