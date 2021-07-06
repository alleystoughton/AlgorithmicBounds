Adversarial Method for Showing Lower Bounds in EasyCrypt
========================================================

This repository contains mechanizations in EasyCrypt of the
adversarial method for showing lower bounds.

This is joint work between Boston University faculty

* [Marco Gaboardi](https://cs-people.bu.edu/gaboardi/) (gaboardi@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)

in collaboration with Boston University doctoral student

* [Weihao Qu](https://www.bu.edu/cs/profiles/weihao-qu/) (weihaoqu@bu.edu)

We have a general EasyCrypt framework for expressing lower bounds problems:

 * [`AdvLowerBounds.eca` - general adversarial lower bounds framework](../main/AdvLowerBounds.eca)

We have completed these lower bounds proofs using the general
framework:

 * [`OrFunctionLB.ec` - application to or function](../main/OrFunctionLB.ec)
 * [`SearchingLB.ec` - application to searching in ordered list](../main/SearchingLB.ec)

We also have a general EasyCrypt framework for expressing upper bounds problems:

 * [`UpperBounds.eca` - general upper bounds framework](../main/UpperBounds.eca)

We also have some [work-in-progress](../main/work-in-progress).
