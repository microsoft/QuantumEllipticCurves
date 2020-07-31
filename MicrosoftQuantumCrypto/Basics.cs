// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

using Microsoft.Quantum.Simulation.Core;
using System;

namespace Microsoft.Quantum.Crypto.Canon
{
    public partial class IsTestable
    {
        public class Native : IsTestable
        {
            static bool IsTestableFunc(QVoid qVoid)
            {
                return true; //testable implementation
                // return false; // untestable (for cost estimates)
            }

            public Native(IOperationFactory m) : base(m) { }

            public override Func<QVoid, bool> Body => IsTestableFunc;
        }
    }

    public partial class IsMinimizeDepthCostMetric
    {
        public class Native : IsMinimizeDepthCostMetric
        {
            static bool IsMinimizeDepthCostMetricFunc(QVoid qVoid)
            {
                return
#if MINIMIZE_DEPTH
                    true;
#else
                    false;
#endif
            }

            public Native(IOperationFactory m) : base(m) { }

            public override Func<QVoid, bool> Body => IsMinimizeDepthCostMetricFunc;
        }
    }

    public partial class IsMinimizeTCostMetric
    {
        public class Native : IsMinimizeTCostMetric
        {
            static bool IsMinimizeTCostMetricFunc(QVoid qVoid)
            {
                return
#if MINIMIZE_T
                    true;
#else
                    false;
#endif
            }

            public Native(IOperationFactory m) : base(m) { }

            public override Func<QVoid, bool> Body => IsMinimizeTCostMetricFunc;
        }
    }

    public partial class IsMinimizeWidthCostMetric
    {
        public class Native : IsMinimizeWidthCostMetric
        {
            static bool IsMinimizeWidthCostMetricFunc(QVoid qVoid)
            {
                return
#if MINIMIZE_WIDTH
                    true;
#else
                    false;
#endif
            }

            public Native(IOperationFactory m) : base(m) { }

            public override Func<QVoid, bool> Body => IsMinimizeWidthCostMetricFunc;
        }
    }
}
