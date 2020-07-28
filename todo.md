# TODOs

## Release checklist

- Run unit test and resource estimator for each cost metric; make sure everything passes
- Review README.md's (build/install) instructions
- Get rid the isogeny-related content? (MicrosoftQuantumCrypto:Isogenies.qs, IsogenyTests.qs, SIKE stuff in TimingTests.qs)
- Get rid of failing unit tests (RippleCarryAdderCDKMExhaustiveReversibleTest, RippleCarryAdderCDKMExhaustiveTest, RippleCarryAdderCDKMReversibleTest) because we don't use the corresponding adder?
- when ready, copy `dev` content to `main`, and make project public

## Canon.qs

- Rename the file to something other than Canon.qs. 
    
    (**Done:** Using Basics.qs for now.)

- Make IsTestable() and CostMetric() compile options?

- FakeOpWithT, FakeOpNoT: This does not seem to be used anywhere. Removed them for now. Was probably used by Fernando to experiment with weird behavior.

- Low-T AND and CCNOT gates. Some are now in the standard libraries.

    [12:02 AM] Mathias Soeken
    For the code you are referring to:

    [12:03 AM] Mathias Soeken
    These operations are now part of the Q# libraries, so you could remove the implementations from your code and directly use these:
​
    [12:03 AM] Mathias Soeken
    <https://docs.microsoft.com/en-us/qsharp/api/qsharp/microsoft.quantum.canon.applyand>
    ApplyAnd operation (Microsoft.Quantum.Canon) - Q# reference - Microsoft QuantumInverts a given target qubit if and only if both control qubits are in the 1 state, using measurement to perform the adjoint operation. Inverts target if and only if both controls are 1, but assume...docs.microsoft.com

    ​[12:03 AM] Mathias Soeken
    <https://docs.microsoft.com/en-us/qsharp/api/qsharp/microsoft.quantum.canon.applylowdepthand>
    ApplyLowDepthAnd operation (Microsoft.Quantum.Canon) - Q# reference - Microsoft QuantumInverts a given target qubit if and only if both control qubits are in the 1 state, with T-depth 1, using measurement to perform the adjoint operation. Inverts target if and only if both controls a...docs.microsoft.com

    ​[12:04 AM] Mathias Soeken
    Also a wrapper is not necessary anymore to change it to CCNOT when performing verification with ToffoliSimulator
​
    [12:05 AM] Mathias Soeken
    I recently added a PR to the libraries (<https://github.com/microsoft/QuantumLibraries/pull/292>) that allows them to be simulated classically when using ToffoliSimulator. Like this, we can have one implementation and do Toffoli simulation efficiently but also do resource estimation with the quantum circuit implementation.
    Simulate ApplyAnd and ApplyLowDepthAnd classically by msoeken · Pull Request #292 · microsoft/QuantumLibrariesThis PR overrides the behavior of ApplyAnd and ApplyLowDepthAnd to use the CCNOT behavior when used with ToffoliSimulator.github.com

    [12:05 AM] Mathias Soeken
    This is not yet in the newest version, but will be there in 2 weeks
​
    [12:05 AM] Mathias Soeken
    You can also use it now with the pre-release: <https://github.com/microsoft/QuantumLibraries#optional-using-prerelease-versions>

    The above should be taken into account. AND gates can be replaced by those gates from the standard libraries.

- OppositeTest: Should this be renamed? It sounds like a Test operation, but maybe it's better to call it OppositeCheck?

## Isogenies.qs

The current plan is to not release this in the first go. It should be relatively easy to release it once the elliptic curve library is out. But we should first write a paper to go with it.

We should leave it in here and make it at least compile with the rest (and possibly test some of it), but remove from the first release.