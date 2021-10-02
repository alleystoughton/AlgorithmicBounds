Sorting a List of Distinct Elements
========================================================

We have applied our general lower and upper bounds frameworks to the
problem of determining how a list of distinct elements must be
permuted in order to be sorted, where an algorithm may only query how
the elements at given list positions are related, but not the elements'
values themselves.

* [`SortingProb.ec` - definition of sorting problem](SortingProb.ec)
* [`SortingLB.ec` - lower bound proof](SortingLB.ec)
* [`SortingUB.ec` - upper bound proof for binary search algorithm](SortingUB.ec)
* [`lower-bounds` - OCaml program for generating and printing out two
   lower-approximations to the target sorting lower bound, plus the
   target itself, for a range of values of list lengths](lower-bounds)
