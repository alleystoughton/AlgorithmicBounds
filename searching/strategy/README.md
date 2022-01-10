Searching for Optimal Adversarial Strategies for Searching Problem
========================================================

We have an [OCaml](https://ocaml.org) program that exhaustively
searches for optimal adversarial strategies for the problem of
searching in an ordered list (possibly containing duplicates) for the
least index where a given element is located.

To build the executable, you should first install
[OCaml](https://ocaml.org), the OCaml Package Manager
[`opam`](https://opam.ocaml.org), [OCaml
Batteries](https://ocaml-batteries-team.github.io/batteries-included/hdoc2/)
and the Dune OCaml build system (https://dune.build).
(You can install OCaml Batteries by running `opam install batteries`,
and you can install Dune by running `opam install dune`.)
The source for the program is in the subdirectory [`src`](src).
The `build` bash script can be used to build the executable,
`strategy`, and the `build-cleanup` bash script will remove the
`_build` directory and the `strategy` executable.

Here is the usage message for the `strategy` program:

```
$ strategy
Usage: strategy [options] univ-size arity element
  -mpl Just print minimum path length
  -minimum-path-length Just print minimum path length
  -help  Display this list of options
  --help  Display this list of options
```

For example, we can search for an optimal strategy where the universe
of list elements has size 2 (elements `a` and `b`), lists to be
searched in have arity (size/length) 3, and where the element to be
searched for is `b`:
```
$ strategy 2 3 b
0 a
  1 a
    done (level = 2)
  2 b
    1 a
      done (level = 3)
1 b
  0 a
    done (level = 2)
  2 b
    0 a
      done (level = 3)
2 b
  0 a
    1 a
      done (level = 3)
  1 b
    0 a
      done (level = 3)

minimum path length: 2
```
The list indices `0`, `1` and `2` in the first column are the possible first
moves of the algorithm, querying the value of the specified list element.
The strategy's response immediately follows. E.g., if the algorithm
queries index `1`, then the adversary responds with the answer `b`.
Continuing from that point, the algorithm can then query index `0` or
`2`, and so on. The game ends when the lower bounds game knows the
answer of the searching function, i.e., the minimum list index where
`b` occurs.

If you only want to know the maximum path length of the strategy, instead
of the details of the strategy, you can run
```
$ strategy -mpl 2 3 b
minimum path length: 2
$ strategy -minimum-path-length 2 3 b
minimum path length: 2
```
