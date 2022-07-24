# Locus
An expert system based upon topos theory.

## Topos theoretic knowledge representation
Developments in elementary copresheaf topos theory suggest a new approach to creating knowledge graphs for systematizing mathematical knowledge. This leads us to two new fundamental primitives.

- Memory locations: congruences in Sets
- Data dependencies: congruences in Sets^(->)

Traditional knowledge graphs are primarily focused on formalising knowledge about subobjects. By extending this with the new theory of congruence lattices of copresheaves, we can create a more effective means of systematizing mathematical knowledge. These same mechanisms can be used to create a mathematical theory of computation.

## Program architecture
We can divide the Locus code base into two components:

* Data visualisation : components for visualising knowledge graphs, copresheaves, and other mathematical objects
* Data processing : mechanisms for raw data processing on algebraic structures, symbolic expressions, and other mathematical objects

## Data visualisation
A JavaFX based graphical user interface is provided to handle the visualisation copresheaves over finitely generated categories. It consists of the generating system of a category displayed as a labeled directed graph and a system of directed graphs associated to each of those generators.

<img width="700" alt="nje" style="border:1px solid black;" src="https://i.ibb.co/bms95TJ/copresheaf-viewer.png">

Clicking on one of the objects or morphisms of the category produces the resulting set or function produced by the copresheaf. The copresheaf viewer also supports panning and zooming using JavaFX transforms.

## Data processing
In addition to our foundational support for topoi, the following more advanced features are implemented:

* support for semigroup theoretic functionality like Green's relations, commuting graphs, subsemigroups, congruences, semigroup homomorphisms, regular semigroups, inverse semigroups, etc
* algorithms for handling finite groups, permutation groups, free groups, etc
* generic lattice theoretic functionality so that any object can be associated to lattices using the sub and con multimethods.
* support for elementary categories, functors, natural transformations, adjunctions, relational functors, arrow categories, subobject classifiers, internal hom, etc.
* elementary topos theory: sets, functions, morphisms of functions, bijections, disets, nsets, quivers, permutable quivers, unital quivers, dependency quivers, compositional quivers, compositional unital quivers, higher arity quivers, MSets, dependency functors, and copresheaves over arbitrary categories
* grothendeick topos theory: sheaves on sites 
* enriched categories such as 2-categories, 2-posets, and categories of modules
* graphs, hypergraphs, incidence structures, and their span copresheaves
* generic arithmetic operations based upon semirings and their specialisations
* a number of basic arithmetical structures like complex numbers, quaternions, matrices, polynomials, rational functions, power series, formal laurent series, elements of semigroup semirings, etc
* support for modules, semimodules, and vector spaces as well as algorithms for treating commutative monoids as semimodules and commutative groups as modules
* support for non-associative generalisations of categories
* the hyperarithmetic of additive partitions
* topoi as foundations of computation
* interfaces with apache commons math 
* an upper ontology of mathematical structures

## Documentation 
A user manual is provided in the documentation folder. It describes our original research into the topos theoretic foundations of computation and their implementation.

## License
Apache license version 2.0

Copyright © 2022 John Bernier

## Version
1.0.5 release

## Contributing
Contributions of tests, documentation, code, ideas, etc are welcome.
