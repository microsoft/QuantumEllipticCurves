// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Basics
{
    using System;
    using Microsoft.Quantum.Simulation.Core;

    public partial class IsMinimizeWidthCostMetric
    {
        public class Native : IsMinimizeWidthCostMetric
        {
            public Native(IOperationFactory m)
                : base(m)
            {
            }

            public override Func<QVoid, bool> __Body__ => IsMinimizeWidthCostMetricFunc;

            public static bool IsMinimizeWidthCostMetricFunc(QVoid qVoid)
            {
                return
#if MINIMIZE_WIDTH
                    true;
#else
                    false;
#endif
            }
        }
    }
}