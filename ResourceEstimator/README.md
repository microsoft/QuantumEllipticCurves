# Resource Estimator

## Running Estimates
This code will run resource estimates at numerous parameter sizes for all basic modular arithmetic operations, as well as elliptic curve operations for Shor's algorithm.

To compare to the results from [Häner et al. 2020](https://eprint.iacr.org/2020/077), the outputs from the elliptic curve operations must be adjusted to account for optimal window sizes. The python script `shor_estimate.py` will do this. It will load the costs from `EllipticCurveEstimates/Low{Depth,T,Width}/Fixed-modulus-signed.csv` and adjust them based on different window sizes, trying all window sizes until it finds the lowest cost. It then writes the resource estimates from this optimal window size to `shor_low_{depth,T,width}_fixed.csv`. It also does the same for smaller window sizes, using hard-coded asymptotic formulas.

## Basic Logic
The goal is to run different operations of the form `Int => Unit()`, where the integer parameter represents some parameter of the function. For example, one operation runs an addition circuit, adding numbers whose bitsize equals the parameter given. 

### ResourceEstimateWrappers.qs
All of these quantum operations are in the "ResourceEstimateWrappers.qs" file. They all have the same format: They allocate qubits, then format them as necessary, then they run a single quantum operation. They may also select random or specified classical inputs as needed. After they are finished, they reset the qubits they borrowed with an operation that asserts an irrelevant measurement property.

Almost all of them use the `ControlledOp` wrapper. This takes a boolean `isControlled` argument, as well as an operation. If `isControlled` is true, this allocates one more qubit and uses it to control the operation. If `isControlled` is false, it simply runs the operation without a control qubit.

### Calling a estimator test from C\#
We want to run many resource estimates with different parameters and on different functions. Thus, we want a single wrapper function that can take a quantum operation as an argument, and will perform the test. Quantum operations are an odd type in C\#. The two types defined in the `Driver` class, `RunQop` and `RunParameterizedQop`, act sort of as type wrappers for quantum operations. 

Thus, given a quantum operation `QuantumOp` of the form `(Int, Bool) => Unit()`, then `QuantumOp.Run` can be created as an object of type `RunQop`. Given an object `runner` of type `RunQop`, it can be called in C\# as `runner(estimator, intValue, boolValue).Result)`, which runs the quantum operation and returns a result type.

The method `SingleResourceTest` does a single test. It takes a quantum operation, formatted as above into a `RunQop` object, as well as several parameters of the test:

	* `locker` is a lock, used to prevent threading issues when writing outputs to the same file
	* `n` is an integer parameter which is passed to the quantum operation
	* `isControlled` is a boolean which is also passed to the quantum operation
	* `filename` is the filename of the file, assumed to be .csv, into which a single line of results will be appended.
	* `full_depth` tells it whether to count all gates when estimating depth, or just T gates.

The `RunQop` object needs a simulator as an argument, which is what governs how it is run. `SingleResourceTest` creates a new simulator object. The simulator object stores all the resource estimates within itself, and thus each different test needs a new simulator. The simulator can output its results in .csv format, and the `DisplayCSV.csv` method formats this into a single, comma-separated string. Finally, `SingleResourceTest` will take this string and append it to the file, after waiting to get a lock on the file.

### Running many estimator tests
The rest of the code in `Driver.cs` just wraps `SingleResourceTest` so that it can be run with many different parameters.

`BasicResourceTest` takes the same arguments as `SingleResourceTest`, except it takes an array of parameters. It creates a .csv file for the results, formats a header row, then calls `SingleResourceTest` with the different parameters. The intended use is that each call to `BasicResourceTest` will write to a different file.

The various methods that begin with `Estimate...` then call `BasicResourceTest` with different quantum operations. The quantum operations are given both as a type parameter and as the first argument. The `Estimate...` methods create a directory given to them as an argument, and then save estimates for related quantum operations (e.g., basic addition) to that directory. These methods also call each quantum operations with both values of `isControlled` and `full_depth`. 

Finally, `Main` will allocate different arrays of parameter sizes, and call the various `Estimate...` methods. 

### Changing optimization strategies
There are currently three different optimization strategies for the quantum circuits: low depth, low width, and low T count. These are set as a compile configuration in the `MicrosoftQuantumCrypto` project. That is, we cannot change the circuit design from within `Driver.cs`. Instead, we must recompile the `MicrosoftQuantumCrypto` library for each desired cost metric. The estimates will be saved in a different directory for each cost metric.

### Windowing Estimation Tests
Running tests for windowing is slightly different, because the quantum operation takes two integer parameters: The original integer parameter (e.g., number of qubits), and a second parameter representing the window sizes. Besides that, everything runs in basically the same way, except we must loop over possible values of the window size. 

The analogous types and methods are:

	* `RunQop` => `RunParameterizedQop`
	* `SingleResourceTest` => `SingleParameterizedResourceTest`
	* `BasicResourceTest` => `ParameterizedResourceTest`
	* `Estimate....` => `Estimate...WindowSizes`

The only other main difference is that we attempt to be efficient in estimating window sizes. We assume that the cost relative to the window size is roughly convex: if we increase the window size from 0, the cost will decrease to a minimum, then strictly increase from that point. Thus, once the cost begins to increase, we would like to stop the tests. Currently this works fine for a single-threaded approach, but not for a multi-threaded approach.

