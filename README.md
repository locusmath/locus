# Locus
A computer algebra system based upon presheaf theory.

## The geometry of memory
Locus is based upon the idea that we can reason logically about the geometry of memory using topos theory.

* Memory locations: congruences in the topos Sets
* Data dependencies: congruences in the topos Sets^(->)

Memory locations and data dependencies are presheaf congruences. This motivates our idea that computation should be modeled using presheaf theory.

## Visualisation of presheaves
A typical presheaf over a partial order can be displayed using Graphviz clusters. Each cluster of nodes represents a set of the copresheaf and the arrows between them represent generating functions. These generalize the box and arrow diagrams typically used for displaying functions.

<img width="500" style="border:1px solid black;" src="https://i.ibb.co/gFW1y3P/triangle.png">

Copresheaves in the topos Sets^(1,2) are used in the topos theory of hypegraphs. Any hypergraph or finite set system produces a corresponding span copresheaf.

<img width="500" style="border:1px solid black;" src="https://i.ibb.co/1GL27JV/span.png">

This method of visualisation works best for copresheaves over partial orders. Otherwise, a JavaFX based graphical user interface is provided to handle the visualisation of copresheaves over finitely generated categories. It displays an interactive quiver that opens up a set or function diagram when you click on its objects or morphisms.

<img width="700" alt="nje" style="border:1px solid black;" src="https://i.ibb.co/ygn314S/Screenshot-20220724-150704.png">

The same technique used in the copresheaf viewer can be used to view globular sets, which associate arbitrary quivers to the hom classes in a directed graph, instead of functions. So alternative mechanisms of visualisations are available for globular sets, which are another important class of presheaf encountered in topos theory.

## Features
Locus is based upon the idea of organizing mathematical theories using presheaf theory. Locus enables computations in presheaf theory.

* support for presheaves over preorders: including the functional dependencies of relations, sets, functions, disets, bijections, difunctions, dibijections, nsets, nfunctions, nbijections, triangles, spans, cospans, diamonds, gems, chains, ditriangles, cubes, trijections, multijections, and so on.
* presheaves over monoids: MSets, GSets, and related structures.
* presheaves over free categories: concrete quiver representations
* support for presheaves over product categories: bicopresheaves, tricopresheaves, the hom functor, etc. Support for presheaves over coproduct categories and the construction of such presheaves by direct sum of simpler presheaves.
* support for a broad variety of presheaves over general categories: quivers, permutable quivers, unital quivers, dependency quivers, ternary quivers, higher arity quivers, functional quivers, compositional quivers, two quivers, n-quivers, path quivers, globular sets, simplicial sets, and presheaves over arbitrary categories.
* support for presheaves over sites: sheaves as a special case in presheaf theory
* functional dataflow analysis using congruence lattices of copresheaves
* support for structure presheaves using functors over concrete categories: presheaves of monoids, presheaves of preorders, presheaves of categories, presheaves of rings, etc
* presheaf based approaches to higher structures using globular and simplicial sets
* presheaf based mechanisms for reasoning about the functional dependencies of relations
* an enriched categories framework with support for a wide variety of types of structure: semiringoids, ringoids, ordered categories, lawvere metrics, two categories, linear categories, etc.
* support for modules as ab-enriched structure presheaves of abelian groups over ringoids.
* generic arithmetic support for a wide variety of data types: complex numbers, quaternions, matrices, polynomials, rational functions, power series, formal laurent series, etc
* basic support for algebraic geometry
* the hyperarithmetic of additive partitions
* interfaces with apache commons math

## Documentation 
A user manual is provided in the documentation folder. It describes our original research into the topos theoretic foundations of computation and their implementation. A revised and updated version of the user manual will be developed soon.

## Authors
John Bernier

## License
Apache license version 2.0

Copyright © 2022 John Bernier

## Version
1.5 release

## Contributing
Contributions are welcome.
