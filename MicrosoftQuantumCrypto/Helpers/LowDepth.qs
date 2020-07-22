namespace Microsoft.Quantum.OracleCompiler.Graphs.LowDepth {
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;

    /// prepares the linear combinations
    ///   a ⊕ c
    ///   b ⊕ c
    ///   c
    ///   a ⊕ b ⊕ c
    /// on the four qubits
    ///   a
    ///   b
    ///   c
    ///   d
    operation LinearPrepare(a : Qubit, b : Qubit, c : Qubit, d : Qubit) : Unit is Adj {
        CNOT(b, d);
        CNOT(c, a);
        CNOT(c, b);
        CNOT(a, d);
    }

    /// c2 c1
    ///  0  0  0
    ///  0  1  0
    ///  1  0  0
    ///  1  1  1
    operation AND(control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...) {
            using (anc = Qubit()) {
                H(target);
                LinearPrepare(control1, control2, target, anc);
                Adjoint T(control1);
                Adjoint T(control2);
                T(target);
                T(anc);
                Adjoint LinearPrepare(control1, control2, target, anc);
                H(target);
                S(target);
            }
        }
        adjoint (...) {
            H(target);
            AssertProb([PauliZ], [target], One, 0.5, "Probability of the measurement must be 0.5", 1e-10);
            if (IsResultOne(M(target))) {
                S(control1);
                S(control2);
                CNOT(control1, control2);
                Adjoint S(control2);
                CNOT(control1, control2);
                Reset(target);
            }
        }
    }

    /// c2 c1
    ///  0  0  0
    ///  0  1  0
    ///  1  0  1
    ///  1  1  0
    operation ANDNP(control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...) {
            using (anc = Qubit()) {
                H(target);
                LinearPrepare(control1, control2, target, anc);
                T(control1);
                Adjoint T(control2);
                T(target);
                Adjoint T(anc);
                Adjoint LinearPrepare(control1, control2, target, anc);
                H(target);
                S(target);
            }
        }
        adjoint (...) {
            H(target);
            AssertProb([PauliZ], [target], One, 0.5, "Probability of the measurement must be 0.5", 1e-10);
            if (IsResultOne(M(target))) {
                Adjoint S(control1);
                S(control2);
                CNOT(control1, control2);
                S(control2);
                CNOT(control1, control2);
                Reset(target);
            }
        }
    }

    /// c2 c1
    ///  0  0  0
    ///  0  1  1
    ///  1  0  0
    ///  1  1  0
    operation ANDPN(control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...) {
            using (anc = Qubit()) {
                H(target);
                LinearPrepare(control1, control2, target, anc);
                Adjoint T(control1);
                T(control2);
                T(target);
                Adjoint T(anc);
                Adjoint LinearPrepare(control1, control2, target, anc);
                H(target);
                S(target);
            }
        }
        adjoint (...) {
            H(target);
            AssertProb([PauliZ], [target], One, 0.5, "Probability of the measurement must be 0.5", 1e-10);
            if (IsResultOne(M(target))) {
                S(control1);
                Adjoint S(control2);
                CNOT(control1, control2);
                S(control2);
                CNOT(control1, control2);
                Reset(target);
            }
        }
    }

    /// c2 c1
    ///  0  0  1
    ///  0  1  0
    ///  1  0  0
    ///  1  1  0
    /// TODO has some relative phase (ignore?)
    operation ANDNN(control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...) {
            using (anc = Qubit()) {
                H(target);
                LinearPrepare(control1, control2, target, anc);
                T(control1);
                T(control2);
                T(target);
                T(anc);
                Adjoint LinearPrepare(control1, control2, target, anc);
                H(target);
                S(target);
            }
        }
        adjoint (...) {
            H(target);
            AssertProb([PauliZ], [target], One, 0.5, "Probability of the measurement must be 0.5", 1e-10);
            if (IsResultOne(M(target))) {
                Adjoint S(control1);
                Adjoint S(control2);
                CNOT(control1, control2);
                Adjoint S(control2);
                CNOT(control1, control2);
                Reset(target);
            }
        }
    }
}
