Sorting a List of Distinct Elements
========================================================

We have applied our general lower and upper bounds frameworks to the
problem of determining how a list of distinct elements must be
permuted in order to be sorted, where an algorithm may only query how
the elements at given list positions are related, but not the elements'
values themselves.

* [`SortingProb.ec` - definition of sorting problem](SortingProb.ec)
* [`SortingLB.ec` - lower bound proof](SortingLB.ec)
* [`SortingUB.ec` - upper bound proof for merge sort algorithm](SortingUB.ec)
* [`ocaml-code` - OCaml programs for carrying out various
   comparisons and other experiments regarding the above](ocaml-code)
