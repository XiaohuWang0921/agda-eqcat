agda-eqcat project
==================
This repository contains the project agda-eqcat, which is a formalisation of category theory in Agda. It differs from [agda-categories](https://github.com/agda/agda-categories) in that in this project, a category is defined with an equality on objects, making it suitable for situations such as _contextual categories_ as presented in Kapulkin & Lumsdain's [paper](https://doi.org/10.4171/JEMS/1050) on Voedovsky's construction for a simplicial model of univalent type theory. Other than that, it draws much inspiration from agda-categories.

It is the hope of the author of this project (me) to one day use it to formalise contextual categories.

Approach
--------
We simply view a category in Agda as an "internal category" in the "category of setoids".