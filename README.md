agda-eqcat project
==================
This repository contains the project agda-eqcat, which is a formalisation of category theory with equality on objects in Agda.

This project came about while I was reading Kapulkin & Lumsdaine's [paper](https://doi.org/10.4171/JEMS/1050) on Voedovsky's construction for a simplicial model of univalent type theory. There, they present the approach based on _contextual categories_, which requires an inherent notion of equality between objects. Based on this project, I hope to one day formalise contextual categories in Agda.

Approach
--------
We simply view a category in Agda as an "internal category" in the "category of setoids".