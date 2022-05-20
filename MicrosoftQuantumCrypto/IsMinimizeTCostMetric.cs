// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Basics
{
    using System;
    using Microsoft.Quantum.Simulation.Core;

    public partial class IsMinimizeTCostMetric
    {
        public class Native : IsMinimizeTCostMetric
        {
            public Native(IOperationFactory m)
                : base(m)
            {
            }

            public override Func<QVoid, bool> __Body__ => IsMinimizeTCostMetricFunc;

            public static bool IsMinimizeTCostMetricFunc(QVoid qVoid)
            {
                return
#if MINIMIZE_T
                    true;
#else
                    false;
#endif
            }
        }
    }
}