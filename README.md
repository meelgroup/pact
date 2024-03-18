[![License: BSD](
    https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](
        https://opensource.org/licenses/BSD-3-Clause)

pact: Partition And Count on Theories
===============================================================================

pact is a hashing based approximate model counter based on cvc5.

This version of the pact is designed to serve as a supplementary tool for a paper currently undergoing peer review. Please refer to [cvc5's readme](README-cvc5.md) for more details about cvc5.

## Build for Counting

```
./configure.sh --auto-download
cd build
make
```

## Use for Counting

Count by enumeration.

`./cvc5 -e <filename>`

Count as pact.

`./cvc5 -S <filename>`

Count with varying epsilon and delta

`./cvc5 -S --delta <value> --epsilon <value> <filename>`

Count with varying starting slicesize

`./cvc5 -S --slicesize <value> <filename>`

Issue `./cvc5 -h` and look for `Model Counting Module` for more options.

Build and Dependencies
-------------------------------------------------------------------------------

pact can be built on Linux and macOS.  For Windows, pact can be cross-compiled using Mingw-w64.

For detailed build and installation instructions on these platforms, see file [INSTALL.rst](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst).

Authors
-------------------------------------------------------------------------------
The counting part of pact is written by [Arijit Shaw](arijitsh.github.io) and [Kuldeep S. Meel](cs.toronto/edu/~meel). pact depends on mammoth work done by cvc5. For a full list of cvc5's authors, please refer to the [AUTHORS](https://github.com/cvc5/cvc5/blob/main/AUTHORS) file.
