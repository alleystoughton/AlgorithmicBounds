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

in collaboration with Boston University doctoral student and now
Monmouth University faculty member

* [Weihao Qu](https://weihaoqu.com) (wqu@monmouth.edu)

and Stuyvesant High School student, BU RISE program intern, and now
MIT undergraduate

* Carol Chen (carol120@mit.edu)

Our preliminary work was reported in the 13th International Conference on
Interactive Theorem Proving (ITP 2022) paper <a
href="https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.30">"Formalizing
Algorithmic Bounds in the Query Model in EasyCrypt"</a>.

Our bounds framework is

 * [`Bounds.eca` - lower and upper bounds framework](Bounds.eca)

and is supplemented by

 * [`IntLog.ec` - working with bounds involving integer logarithms](IntLog.ec)
 * [`FSetAux.ec` - auxiliary lemmas on finite sets](FSetAux.ec)
 * [`FRange.ec` - finite ranges as sets](FRange.ec)
 * [`AllLists.ec` - generating all lists of given length over finite universe](AllLists.ec)

We have applied our bounds framework to

 * [proving a lower bound for computing the or (disjunction)
   function of a list of booleans](OrFunctionLB.ec)

 * [proving a lower bound for searching for the least index into an
   ordered list (in which duplicate elements are allowed) where a
   given element is located, as well as proving an identical upper bound for
   the binary search algorithm for this problem](searching)

 * [proving a lower bound for determining how a list of distinct
    elements must be permuted in order to be sorted, as well as proving
    an upper bound for the merge sort algorithm, where an algorithm
    may only query how elements are related, but not the elements'
    values themselves](sorting)
