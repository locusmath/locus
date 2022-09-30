# Locus
An expert system based upon presheaf topos theory.

## Visualisation of presheaves
A typical presheaf over a partial order can be displayed using Graphviz clusters. Each cluster of nodes represents a set of the copresheaf and the arrows between them represent generating functions. These generalize the box and arrow diagrams for typically functions.

<img width="500" style="border:1px solid black;" src="https://i.ibb.co/gFW1y3P/triangle.png">

The resulting diagram is like an extended Hasse diagram with clusters instead of nodes. Here is another example from the topos Sets^(2,1).

<img width="500" style="border:1px solid black;" src="https://i.ibb.co/mF94BTj/cospan.png">

Copresheaves in the topos Sets^(1,2) are used in the topos theory of hypegraphs. Any hypergraph or finite set system produces a corresponding span copresheaf.

<img width="500" style="border:1px solid black;" src="https://i.ibb.co/1GL27JV/span.png">

This method of visualisation works best for copresheaves over partial orders. Otherwise, a JavaFX based graphical user interface is provided to handle the visualisation of copresheaves over finitely generated categories. It displays an interactive quiver that opens up a set or function diagram when you click on its objects or morphisms.

<img width="700" alt="nje" style="border:1px solid black;" src="https://i.ibb.co/ygn314S/Screenshot-20220724-150704.png">

The same technique used in the copresheaf viewer can be used to view globular sets, which associate arbitrary quivers to the hom classes in a directed graph, instead of functions. So alternative mechanisms of visualisations are available for globular sets, which are another important class of presheaf encountered in topos theory.

## Mathematical features
Locus is based upon the idea of organizing mathematical theories using presheaf theory. Presheaves can be reasoned about using topos theory.

* basic support for presheaves over preorders: including the functional dependencies of relations, sets, functions, disets, bijections, difunctions, dibijections, nsets, nfunctions, nbijections, triangles, spans, cospans diamonds, gems, chains, ditriangles, cubes, trijections, multijections, and so on.
* fundamental support for presheaves over monoids: MSets, GSets, and related structures.
* support for a broad variety of presheaves over general categories: quivers, permutable quivers, unital quivers, dependency quivers, ternary quivers, higher arity quivers, functional quivers, compositional quivers, two quivers, n-quivers, path quivers, globular sets, simplicial sets, and presheaves over arbitrary categories.
* support sheaves over sites
* computations involving subobject and congruence lattices of copresheaves
* functional dataflow analysis using congruence lattices of copresheaves
* widespread use of concrete categories throughout the system for use in presheaf theory
* extensive built in support for structure copresheaves over a wide variety of concrete categories: presheaves of groups, presheaves of rings, etc
* an overall ontology of mathematics based upon structured presheaves: structured sets, structured functions, structured pairs of sets, structured pairs of functions, structured quivers, structure presheaves, structure sheaves, etc.
* presheaf theoretic approaches to higher structures using globular and simplicial sets. Two-categories as structured two-globular sets.
* generic arithmetic operations based upon rings and semirings
* a number of basic arithmetical structures like complex numbers, quaternions, matrices, polynomials, rational functions, power series, formal laurent series, etc
* basic support for algebraic varieties and their coordinate rings
* support for modules, semimodules, and vector spaces as well as algorithms for treating commutative monoids as semimodules and commutative groups as modules
* the hyperarithmetic of additive partitions
* interfaces with apache commons math

## Geometric philosophy
Computer science is like geometry. Instead of spatial locations, we deal with memory locations and memory addresses. Presheaf topos theory is the fundamental means we have of reasoning about these memory addresses, just as it is the key means we have of reasoning about spatial locations in geometry. Topos theory is not only the key to algebraic geometry, it is also the key to understanding computation as well.

## Documentation 
A user manual is provided in the documentation folder. It describes our original research into the topos theoretic foundations of computation and their implementation.

## Authors
John Bernier

## License
Apache license version 2.0

Copyright © 2022 John Bernier

## Version
1.2.0 release

## Contributing
Contributions are welcome.
