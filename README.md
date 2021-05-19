Adversarial Method for Showing Lower Bounds in EasyCrypt
========================================================

This repository contains mechanizations in EasyCrypt of the
adversarial method for showing lower bounds.

This is joint work between Boston University faculty

* [Marco Gaboardi](https://cs-people.bu.edu/gaboardi/) (gaboardi@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)

We have a general EasyCrypt framework for expressing lower bound problems:

 * [`AdvLowerBounds.ec` - generic adversarial lower bounds framework](../main/AdvLowerBounds.ec)

We have fully worked out these examples using the general framework:

 * [`OrFunction.ec` - application to or function](../main/OrFunction.ec)
 * [`Searching.ec` - application to searching in ordered list](../main/Searching.ec)

We also have some [work-in-progress](../main/work-in-progress).
