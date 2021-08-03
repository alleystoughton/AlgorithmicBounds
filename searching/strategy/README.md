Searching for Optimal Adversarial Strategies for Searching Problem
========================================================

We have an [OCaml](https://ocaml.org) program that exhaustively
searches for optimal adversarial strategies for the problem of
searching in an ordered list (possibly containing duplicates) for the
least index where a given element is located.

To build the executable, you should first install
[OCaml](https://ocaml.org), the OCaml Package Manager
[`opam`](https://opam.ocaml.org), and [OCaml
Batteries](https://ocaml-batteries-team.github.io/batteries-included/hdoc2/).
(You can install OCaml Batteries by running `opam install batteries`.)
The `build` bash script can be used to build the executable,
`strategy`.

Here is the usage message for the `strategy` program:

```
$ strategy
Usage: strategy [options] univ-size arity element
  -mpl Just print minimum path length
  -minimum-path-length Just print minimum path length
  -help  Display this list of options
  --help  Display this list of options
```
