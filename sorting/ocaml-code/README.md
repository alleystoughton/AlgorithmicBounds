OCaml Code Relating to Comparison-based Sorting
========================================================

This directory contains several OCaml programs relating to
comparison-based sorting. See comments in the files for details.

* [`merge-sort-compare.ml` - comparing the worst case number of
   comparisons used by merge sort with the wc recurrence and its
   upper-approximation](merge-sort-compare.ml)
* [`bounds-compare.ml` - comparing the two lower-approximations to the
   target sorting lower bound, plus the target itself, comparing best
   lower bound with best upper bound, and comparing wc recurrence with
   upper approximation](bounds-compare.ml)
* [`sorting-standard-strategy.ml` - simulating lower bound game
   executions for our adversary and over all query sequences, returning
   the minimum final stage numbers](sorting-standard-strategy.ml)
