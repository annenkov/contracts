# Certified Symbolic Multi-Party Contracts Management and Compilation [![Build Status](https://travis-ci.org/annenkov/contracts.svg?branch=master)](https://travis-ci.org/annenkov/contracts)

An extension of the Contract DSL presented in [ICFP 2015 paper](doc/icfp2015.pdf)
with templating features, and certified compilation to a simple intermediate
payoff expression language (PEL). This expression language can be used to obtain
so called "payoff expression" for using in a context of a "pricing engine"
(software, that uses probabilistic modeling of possible future contract price
using Monte-Carlo simulation). We use Coq to prove soundness of the compiler
from the Contract DSL to PEL, and use Coq's code extraction feature, to obtain
correct Haskell implementation of the compiler.

The [NWPT'16 abstract](http://dannenkov.me/papers/NWPTPayoffLang.pdf) and
presentation slides([slides 1](http://dannenkov.me/papers/NWPT16Slides.pdf),
[slides 2](http://dannenkov.me/papers/HIPERFIT_Workshop_2016.pdf))
outlining the ideas and motivation for the payoff expression language (PEL).

The Coq-based certified implementation of the language is
found in the [Coq](Coq) subdirectory. The [Coq/Payoff](Coq/Payoff) subdirectory
contains the implementation of payoff expression language and compilation
from from the Contract DSL to PEL along with soundness proofs.
The contract language and payoff expression language implementations are documented
in the accompanying README files ([readme for Contracts DSL](Coq/README.md),
[readme for Payoff language](Coq/Payoff/README.md)), which provide an overview of the Coq
proofs. Moreover, this repository also includes earlier prototype
implementations of the contract language in Haskell (see
[Haskell](Haskell) subdirectory) and Standard ML (see [SML](SML)
subdirectory).
