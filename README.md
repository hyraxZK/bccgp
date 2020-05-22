# libbccgp - BCCGP-srqt and Bulletproofs implementations #

**Note**: this library is slower than optimized implementations of bulletproofs, notably
[dalek-cryptography/bulletproofs](https://github.com/dalek-cryptography/bulletproofs).
Please use that library when benchmarking Bulletproofs! (But you may find [libbccgp/pws.py](libbccgp/pws.py)
useful as a way of compiling circuits to the arithmetization that Bulletproofs requires.)

This library contains indepent re-implementations of the following two protocols:

[BCCGP-sqrt](https://eprint.iacr.org/2016/263), from 
J. Bootle, A. Cerulli, P. Chaidos, J. Groth, and C. Petit.
"Efficient Zero-Knowledge Arguments for Arithmetic Circuits in the Discrete Log Setting".
EUROCRYPT, May 2016.

[Bulletproofs](https://eprint.iacr.org/2017/1066), from
B. Bünz, J. Bootle, D. Boneh, A. Poelstra, and G. Maxwell.
"Bulletproofs: Short Proofs for Confidential Transactions and More".
IEEE S&P, May 2018.

In addition, it contains a compiler from (a subset of) PWS files to the constraint
format required by the above two systems.

This implementation is written in Python and C/C++. It is compatible with both Python 2.7
and PyPy. (Porting to Python 3.0 would be trivial, but would reduce performance.)

## Building and using ##

The code in this directory is pure Python, but for elliptic curve operations and
polynomial multiplication, we use C extensions. The EC extension lives in its own repository,
[pymiracl](https://github.com/hyraxZK/pymiracl).
The easiest way to use the whole system is to check out the
[hyraxZK](https://github.com/hyraxZK/hyraxZK) "meta-repository", which links all the necessary
submodules and has a top-level Makefile.

## Running ##

If you want to run a PWS file, you should use `run_fennel.py` like so:

    ./run_bccgp.py -p /path/to/PWS/file

Execute `./run_bccgp.py` with no arguments to see all of the possible arguments.

# License #

Copyright 2017 Riad S. Wahby <rsw@cs.stanford.edu> and the Hyrax authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

# Questions? #

    rsw@cs.stanford.edu
