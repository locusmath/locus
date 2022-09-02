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

<img width="700" alt="nje" style="border:1px solid black;" src="https://i.ibb.co/ygn314S/Screenshot-20220724-150704.png">

Clicking on one of the objects or morphisms of the category produces the resulting set or function produced by the copresheaf. The copresheaf viewer also supports panning and zooming using JavaFX transforms.

## Data processing
The features of Locus fall into two main areas: topos theory and commutative algebra. In particular, the following features have been implemented:

* broad support for categories including preorders, lattices, monoids, and groups as special cases.
* support for a wide variety of copresheaves: sets, functions, bijections, disets, nsets, nfunctions, nbijections, triangles, diamonds, gems, quivers, permutable quivers, unital quivers, dependency quivers, compositional quivers, compositional unital quivers, higher arity quivers, spans, cospans, MSets, GSets, simplicial sets, dependency functors, and copresheaves over arbitrary categories
* computations involving subobject and congruence lattices of copresheaves
* dataflow analysis using congruence lattices of copresheaf topoi
* builtin support for sheaves on sites 
* extensive built in support for structure presheaves over a wide variety of concrete categories 
* support for structure sheaves as a special case of structure presheaves
* an overall ontology of mathematics based upon structured presheaves: structured sets, structured functions, structured pairs of sets, structured pairs of functions, structured quivers, structure presheaves, structure sheaves, etc.
* a library of a wide variety of structured sets 
* enriched categories such as 2-categories, 2-posets, and abelian categories of R-modules
* generic arithmetic operations based upon rings and semirings
* a number of basic arithmetical structures like complex numbers, quaternions, matrices, polynomials, rational functions, power series, formal laurent series, etc
* builtin support for semigroup algebras over a variety of rings and semirings
* support for modules, semimodules, and vector spaces as well as algorithms for treating commutative monoids as semimodules and commutative groups as modules
* the hyperarithmetic of additive partitions
* interfaces with apache commons math

## Documentation 
A user manual is provided in the documentation folder. It describes our original research into the topos theoretic foundations of computation and their implementation.

## License
Apache license version 2.0

Copyright © 2022 John Bernier

## Version
1.1.0 release

## Contributing
Contributions are welcome.
