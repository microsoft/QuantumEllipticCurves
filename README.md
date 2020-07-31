# QuantumEllipticCurves

## Overview

The Quantum Elliptic Curves project contains Q# implementations of quantum elliptic curves primitives, and can be used to obtain resource estimates for the quantum elliptic curve discrete logarithms algorithm (as described in [1]).

The project depends on version 0.11.2006.403 of the [Microsoft Quantum Development Kit](https://www.microsoft.com/en-us/quantum/development-kit). It can be built using [Visual Studio](https://visualstudio.microsoft.com/) or the [.NET CLI](https://docs.microsoft.com/en-us/dotnet/core/tools/).

The code was developed by [Microsoft Research](http://research.microsoft.com/) for experimentation purposes.

[1] Thomas Häner, Samuel Jaques, Michael Naehrig, Martin Roetteler, and Mathias Soeken, "Improved quantum circuits for elliptic curve discrete logarithms".
To appear in: Int'l Conf. on Post-Quantum Cryptography (PQCrypto 2020).
Preprint available at [`https://arxiv.org/abs/2001.09580`](https://arxiv.org/abs/2001.09580).

## Contents

The Quantum Elliptic Curves Visual Studio solution contains the following projects:

### MicrosoftQuantumCrypto

The `MicrosoftQuantumCrypto` project implements the crypographic primitives in Q# and contains unit tests that can be run using Visual Studio's Test Explorer or the .NET CLI (as demonstrated below).

To build the project (with `<CONFIG>` set to `MinimizeDepth`, `MinimizeT`, or `MinimizeWidth`):

`dotnet build -c <CONFIG> .\MicrosoftQuantumCrypto\MicrosoftQuantumCrypto.csproj`

To run the unit tests:

`dotnet test .\MicrosoftQuantumCrypto\MicrosoftQuantumCrypto.csproj`

+++ TODO: MORE DETAILS +++

### ResourceEstimator

+++ TODO: MORE DETAILS +++

The `ResourceEstimator` project creates quantum resource estimates for the `MicrosoftQuantumCrypto` library, using the cost metric with which the library was compiled.

To build the project (with `<CONFIG>` set to `Debug` or `Release`):

`dotnet build -c <CONFIG> .\ResourceEstimator\ResourceEstimator.csproj`

To run the estimator:

`.\ResourceEstimator\bin\<CONFIG>\netcoreapp3.1\ResourceEstimator.exe`

## Contributors

- Samuel Jaques
+++ TODO: who else +++

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
