
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Basics
{
    using System;
    using Microsoft.Quantum.Simulation.Core;

    public partial class IsMinimizeDepthCostMetric
    {
        public class Native : IsMinimizeDepthCostMetric
        {
            public Native(IOperationFactory m)
                : base(m)
            {
            }

           public override Func<QVoid, bool> __Body__ => IsMinimizeDepthCostMetricFunc;

            public static bool IsMinimizeDepthCostMetricFunc(QVoid qVoid)
            {
                return
#if MINIMIZE_DEPTH
                    true;
#else
                    false;
#endif
            }
        }
    }
}
