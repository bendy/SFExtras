This repository holds formalizations of a variety of programming
language topics in the style of Software Foundations.

To use, you'll need a copy of the latest version of [Software
Foundations](https://softwarefoundations.cis.upenn.edu/). Once that is
installed, you'll need to update the _CoqProject file to point LF and
PLF to the locations of Volumes 1 + 2 of Software Foundations. With
that done, running `make` in the top-level directory will build everything.

## ChurchEncodings
A deeply embedded formalization of the untyped lambda calculus with
natural numbers, as well as a number of examples of church-encoded
datatypes (namely booleans, pairs, natural numbers, and lists).

- LCNat.v: a formalization of the untyped lambda calculus with natural numbers
- Church.v: several church encoding examples

## DenotationalSemantics
The denotational semantics of a simple imperative language.

- Fixpoints.v: basics of fixpoints of monotone functions
- Denotational.v: denotational semantics of Imp from Software Foundations
