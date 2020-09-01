// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Basics
{
    using System;
    using Microsoft.Quantum.Simulation.Core;

    public partial class IsTestable
    {
        public class Native : IsTestable
        {
            public Native(IOperationFactory m)
                : base(m)
            {
            }

            public override Func<QVoid, bool> Body => IsTestableFunc;

            public static bool IsTestableFunc(QVoid qVoid)
            {
                return true; // testable implementation

                // return false; // untestable (for cost estimates)
            }
        }
    }
}
