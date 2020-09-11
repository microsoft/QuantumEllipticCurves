# QuantumEllipticCurves

The QuantumEllipticCurves project contains Q# implementations of quantum circuits for elliptic curve arithmetic and isogeny computation.

## Shor's algorithm for computing elliptic curve discrete logarithms

The code provides all operations to obtain resource estimates for quantum circuits to compute elliptic curve discrete logarithms using Shor's algorithm as described in [1] and [2]. Building on integer and modular arithmetic such as modular multiplication, squaring and inversion, the project contains circuits for adding elliptic curve points on Weierstraß curves over prime fields.

## Computing supersingular isogenies

Operations for field arithmetic of quadratic extension fields, Montgomery curve arithmetic over such fields, and circuits for 2-isogeny computations are used to construct circuits for isogeny computations on supersingular elliptic curves as used in SIDH [3] and SIKE [4]. 

The project depends on version 0.12.20082513 of the [Microsoft Quantum Development Kit](https://www.microsoft.com/en-us/quantum/development-kit). It can be built using [Visual Studio](https://visualstudio.microsoft.com/) or the [.NET CLI](https://docs.microsoft.com/en-us/dotnet/core/tools/).

The code was developed by [Microsoft Research](http://research.microsoft.com/) for experimentation purposes.

## Contents

The Quantum Elliptic Curves Visual Studio solution contains the following projects:

### MicrosoftQuantumCrypto

The `MicrosoftQuantumCrypto` project implements the crypographic primitives in Q# and contains unit tests that can be run using Visual Studio's Test Explorer or the .NET CLI (as demonstrated below).

To build the project (with `<CONFIG>` set to `MinimizeDepth`, `MinimizeT`, or `MinimizeWidth`):

`dotnet build -c <CONFIG> .\MicrosoftQuantumCrypto\MicrosoftQuantumCrypto.csproj`

To run the unit tests:

`dotnet test .\MicrosoftQuantumCrypto\MicrosoftQuantumCrypto.csproj`

### ResourceEstimator

The `ResourceEstimator` project creates quantum resource estimates for the `MicrosoftQuantumCrypto` library, using the cost metric with which the library was compiled.

To build the project (with `<CONFIG>` set to `Debug` or `Release`):

`dotnet build -c <CONFIG> .\ResourceEstimator\ResourceEstimator.csproj`

To run the estimator:

`.\ResourceEstimator\bin\<CONFIG>\netcoreapp3.1\ResourceEstimator.exe`

For more details, see `ResourceEstimator\README.md`.

### Issue with estimating resources

A problem with the ResourcesEstimator functionality in Q# has been found and reported in [Issue #192](https://github.com/microsoft/qsharp-runtime/issues/192). Currently, results may report independent lower bounds on depth and width that may not be simultaneously realizable in a quantum circuit. The Q# team has stated that they are working to resolve this issue.

## Contributors

- Samuel Jaques (main contributor)
- Michael Naehrig
- Christian Paquin

## References

[1] Thomas Häner, Samuel Jaques, Michael Naehrig, Martin Roetteler, and Mathias Soeken: "Improved quantum circuits for elliptic curve discrete logarithms".
Post-Quantum Cryptography – PQCrypto 2020, Lecture Notes in Computer Science 12100, Springer-Verlag (2020), pp 425–444.
[`https://eprint.iacr.org/2020/077`](https://eprint.iacr.org/2020/077).

[2] Martin Roetteler, Michael Naehrig, Krysta M. Svore, and Kristin Lauter: "Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms".
Advances in Cryptology – ASIACRYPT 2017, Lecture Notes in Computer Science 10625, Springer-Verlag (2017), pp 241–272.
[`https://eprint.iacr.org/2017/598`](https://eprint.iacr.org/2017/598).

[3] David Jao and Luca DeFeo, "Towards quantum-resistant cryptosystems from supersingular elliptic curve isogenies". Post-quantum cryptography – PQCrypto 2011, Lecture Notes in Computer Science 7071, pp. 19-34, 2011.
[`https://eprint.iacr.org/2011/506`](https://eprint.iacr.org/2011/506).

[4] Reza Azarderakhsh, Matthew Campagna, Craig Costello, Luca De Feo, Basil Hess, Amir Jalali, David Jao, Brian Koziel, Brian LaMacchia, Patrick Longa, Michael Naehrig, Geovandro Pereira, Joost Renes, Vladimir Soukharev, and David Urbanik, "Supersingular Isogeny Key Encapsulation". Submission to the NIST Post-Quantum Standardization project, 2017.
['https://sike.org'](https://sike.org)

## License

The QuantumEllipticCurves project is licensed under the MIT License; see [`License`](LICENSE) for details.

## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.
