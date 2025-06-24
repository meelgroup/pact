[![License: BSD](
    https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](
        https://opensource.org/licenses/BSD-3-Clause)

pact: Partition And Count on Theories
===============================================================================

pact is a hashing-based projected approximate model counter for hybrid SMT formulas. pact takes input an SMT formula over any theory combination and returns the count projected over bitvector and Boolean variables. Please refer to our DAC'25 [paper](https://arijitsh.github.io/assets/pdf/DAC25-count-beyond-discrete.pdf) for details about pact.

## Build for Counting

```
./configure.sh --auto-download --cryptominisat 
cd build
make
```

## Use for Counting


Count as pact, projected on bitvectors.

`./cvc5 -S --hashsm xor <filename>`

Count as pact, projected on Booleans

`./cvc5 -S --projcount <filename>`

Count with different hashing mode

`./cvc5 -S --hashsm prime` or `./cvc5 -S --hashsm shift`

Count with varying epsilon and delta

`./cvc5 -S --delta <value> --epsilon <value> <filename>`

Count with varying starting slicesize

`./cvc5 -S --slicesize <value> <filename>`


Count by enumeration.

`./cvc5 -e <filename>`

Issue `./cvc5 -h` and look for `Model Counting Module` for more options.

Build and Dependencies
-------------------------------------------------------------------------------

pact can be built on Linux and macOS.  For Windows, pact can be cross-compiled using Mingw-w64.

For detailed build and installation instructions on these platforms, see file [INSTALL.rst](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst).

Authors
-------------------------------------------------------------------------------
The counting part of pact is written by [Arijit Shaw](arijitsh.github.io) and [Kuldeep S. Meel](cs.toronto/edu/~meel). pact depends on mammoth work done by cvc5. For a full list of cvc5's authors, please refer to the [AUTHORS](https://github.com/cvc5/cvc5/blob/main/AUTHORS) file. Please refer to [cvc5's readme](README-cvc5.md) for more details about cvc5.

