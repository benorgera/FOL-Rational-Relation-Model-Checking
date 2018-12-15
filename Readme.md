# Getting Started

This tool provides tools to model check rational structures, supporting transitive closure product constructions and Rabin-Scott determinizations, allowing one to check the validity of formulas in Presburger Arithmetic. In addition to these core algorithms, the library provides functions for constructing the foundational machines needed for model checking the naturals, and provides +, -, <, =, = 1 built in. There are also debug tools provided for running machines and testing machines, along with certain abstractions allowing easier construction of meaningful transducers.

# The Transducer Data Structure

The first realization which allowed such a simple implementation of these FSMs was that if you only care to model check Presburger Arithmetic, you can use a `0` in place of a `#`. This is true because padding with leading zeros doesn't change the numerical value of the input, so any arithmetic operation on `x#...#` must have the same behavior on `x0...0` (this observation trivially generalizes to multiple tracks). So we may assume **2** is our alphabet, allowing for much simpler, smaller machines.

It is useful to overload the word character (w.r.t. a certain `k`-track machine) to mean the set of all tuples of characters of length `k`. So each state has 2^`k` transitions, and we can think of each character as the number it encodes in binary. Machines are encoded as adjacency lists where state `i` has an array mapping these indexed characters to other states, and are always deterministic. The Rabin-Scott procedure need merely be passed which labels were erased to pretend that a machine is nondeterministic.

By maintaining the invariant that all machines are accessible (the base case machines are accessible, and every construction is a transitive closure), we can check in constant time whether a `k`-track machine accepts any, or rejects all of its inputs, simply by checking the size of the set of final states. Seeing as we construct our machine using closure operations, all transitions can only be in the set of vertices discovered so far, so 8-bit integer arrays are used for the transition table initially, and the size is increased as needed, to ensure compact machines.

Each track on a machine is associated with a label (typically an algebraic variable name such as `x` or `y`), so that each track can be thought to correspond to a variable in our formula, allowing for the abstraction of product constructions over formula, where the two relations can have different numbers of arguments and may or may not both reference a given variable. Hence we can take the and/or product of an `(x, y, z)` relation with a `(z, x, w)`, and the construction handles both projections and ignoring certain tracks for us.

# Usage

The model checking module can be included by any Node.js script in its directory via
```javascript
var MC = require('./ModelChecking')
```
The base case transducers can be accessed via ```MC.Transducers.NAMEOFMACHINE```, and the file `Transducers.js` provides insight into their structure, and also allows for adding new base cases to the library.

The products of machines `M1` and `M2` can be taken via ```MC.AND(M1, M2)```, ```MC.OR(M1, M2)``` non-destructively, both in ```O(n^2)``` time if we assume the number of tracks to be fixed. The track labeled `x` in `M` can be erased without destructing ```M``` to yield a relation with one fewer component via `MC.EXISTS(['x'], M)`, and this array can be extended with more labels to allows for running the powerset construction with multiple tracks (this is ```O(2^n)``` and gets noticeably worse if our machine has many tracks). ```MC.FORALL``` is symmetric, and uses ```MC.NOT(T)``` to apply the not-exists-not property. Negation is done in constant time because of the determinism invariant, and is also non-destrictive. ```MC.SAT(T)``` allows for a constant time check to whether ```T``` has any reachable final states, and is logically equivalent to erasing all labels using ```MC.EXISTS```.

Additionally the functions ```MC.timesConstant(k, inputLabel, outputLabel, determinize)``` and ```MC.linearDiophantine(A, B, determinize)``` construct the machines accepting ```(x, y)``` iff ```x * k = y``` in the former case, and iff ```x * A - y * B = 1``` in the latter. Both machines provide a ```determinize``` flag signaling to run Rabin-Scott every time a variable we no longer need appears in our machine, whereas without this, all unneeded tracks are erased at the end in one powerset run. Experimentally this flag has proven essential for larger machines, because the cost incurred by the number of tracks is by no means negligible. Machines can be run and tested using ```MC.run``` and ```MC.testArithmetic```, as shown below:
```javascript
var T7 = MC.timesConstant(7, 'x', 'y', false);
console.log('7(8) = 56: ' + MC.run(['0001', '000111'], T7));
console.log('Bulk Test: ' + MC.testArithmetic(T7, (x, y) => 7 * x === y, 6));
```
The last argument to testArithmetic specifies that every combination of numbers less than ```2^6``` be fed as input to ```T``` (the encoding of the numbers go to ```T```, but the values go to the lambda).

# Learn More

The file ```test.js``` is very useful and walks through usage of all non-obvious functions in the interface of this model checker. For a full list of functions, the bottom of ```ModelCheck.js``` lists all exports, including some useful utility functions.

To run the test script, download Node.js and in the project directory, run 
```
node test.js
```
If you are looking to model check larger structures (upwards of a million states), it is recommended that any node threads using the library give additional memory by specifying
```
node --max-old-space-size=4096 MYSCRIPT.js
```
It is worth noting that as of right now the max supported state complexity is ```2^32 - 1```, as this is the maximum length javascript array. Checkout out the ```constructions``` directory to see an example of just how fast these machines can blow up.


 