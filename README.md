EasyCrypt Frameworks for Proving Algorithmic Bounds
========================================================

This repository contains a general
[EasyCrypt](https://www.easycrypt.info/trac/) framework for expressing
worst case lower bounds problems using the adversarial method
(adversary arguments), a general EasyCrypt framework for expressing
worst case upper bounds of algorithms, and applications of these
frameworks.

This is joint work between Boston University faculty

* [Mark Bun](https://cs-people.bu.edu/mbun/) (mbun@bu.edu)
* [Marco Gaboardi](https://cs-people.bu.edu/gaboardi/) (gaboardi@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)

in collaboration with Boston University doctoral student

* [Weihao Qu](https://www.bu.edu/cs/profiles/weihao-qu/) (weihaoqu@bu.edu)

and Stuyvesant High School student and BU RISE program intern

* Carol Chen (cchen20@stuy.edu)

We have general EasyCrypt frameworks for expressing lower and
upper bounds problems

 * [`Bounds.eca` - lower and upper bounds frameworks](../main/Bounds.eca)

We have applied these frameworks to

 * [proving a lower bound for computing the or (disjunction)
   function of a list of booleans](../main/OrFunctionLB.ec)

 * [proving a lower bound for searching for the least index into an
   ordered list (in which duplicate elements are allowed) where a
   given element is located, as well as proving an upper bound for
   the binary search algorithm for this problem](../main/searching)

 * [proving a lower bound for determining how a list of distinct
    elements must be permuted in order to be sorted, as well as proving
    an upper bound for the merge sort algorithm, where an algorithm
    may only query how elements are related, but not the elements'
    values themselves](../main/sorting)
