EasyCrypt Framework for Proving Algorithmic Bounds in Query Model
=================================================================

This repository contains a general
[EasyCrypt](https://github.com/EasyCrypt/easycrypt) framework for
expressing computational problems in the query model, and for proving
worst case lower bounds for computational problems using the
adversarial method (adversary arguments), and proving worst case upper
bounds for algorithms solving the computational problems.

This is joint work between Boston University faculty

* [Mark Bun](https://cs-people.bu.edu/mbun/) (mbun@bu.edu)
* [Marco Gaboardi](https://cs-people.bu.edu/gaboardi/) (gaboardi@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)

in collaboration with Boston University doctoral student

* [Weihao Qu](https://www.bu.edu/cs/profiles/weihao-qu/) (weihaoqu@bu.edu)

and Stuyvesant High School student and BU RISE program intern

* Carol Chen (cchen20@stuy.edu)

Our bounds framework is

 * [`Bounds.eca` - lower and upper bounds framework](../main/Bounds.eca)

and is supplemented by

 * [`IntLog.ec` - working with bounds involving integer logarithms](IntLog.ec)
 * [`FSetAux.ec` - auxiliary lemmas on finite sets](FSetAux.ec)
 * [`FRange.ec` - finite ranges as sets](FRange.ec)
 * [`AllLists.ec` - generating all lists of given length over universe](AllLists.ec)
 * [`WF.ec` - well founded relations, induction and recursion)(WF.ec)

We have applied our bounds framework to

 * [proving a lower bound for computing the or (disjunction)
   function of a list of booleans](../main/OrFunctionLB.ec)

 * [proving a lower bound for searching for the least index into an
   ordered list (in which duplicate elements are allowed) where a
   given element is located, as well as proving an identical upper bound for
   the binary search algorithm for this problem](../main/searching)

 * [proving a lower bound for determining how a list of distinct
    elements must be permuted in order to be sorted, as well as proving
    an upper bound for the merge sort algorithm, where an algorithm
    may only query how elements are related, but not the elements'
    values themselves](../main/sorting)
