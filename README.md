# Locus
A specialised computer algebra system for presheaf theory.

## Geometry of memory
Memory locations and their relations are abstractly modeled using presheaf congruences. 

* Memory locations: congruences in Sets
* Data dependencies: congruences in Sets^(->)

## Presheaf constructions
Classical mathematics defined a number of constructions on sets. We can start by generalizing these to presheaves.

| Sets               | Presheaves               |
|--------------------|--------------------------|
| Subsets            | Subobjects               |
| Partitions         | Congruences              |
| Ordered sets       | Presheaves of posets     |
| Topological spaces | Presheaves of topologies |
| Rings              | Presheaves of rings      |
| Structured sets    | Structure presheaves     |

The point is to determine as much as possible what constructions look like on presheaves instead of sets. So an example of this is that we can take the lattice of preorders previously defined on sets, and now define a lattice of preorders for any presheaf whose objects are presheaves of preorders. This applies to most structures which have presheaf generalisations.

Topos theory allows us to generalize several constructions from sets to presheaves. Set predicates correspond to subobject classifiers. Limits and colimits of sets can be generalized to presheaves. Structures on sets can be generalized to structures on presheaves, or to internal structures in a presheaf topos.

## Presheaf visualisations
Locus can visualize presheaves of sets in one of two ways. The first is all at once using Graphivz clusters like below.

<img width="300" style="border:1px solid black;" src="https://i.ibb.co/gFW1y3P/triangle.png">

This works well for presheaves over partial orders. The category of elements, and its object preorder can be visualized for such simple presheaves. The second way they can be visualized is with the JavaFX viewer which lets you look at the functions of the presheaf one at a time:

<img width="500" alt="nje" style="border:1px solid black;" src="https://i.ibb.co/ygn314S/Screenshot-20220724-150704.png">

Separate visualisation routines are available for different types of presheaves of structures. Presheaves of unary relations are visualised by highlighting all elements in each unary relation a different color. Presheaves of setoids are visualised by using nested graphviz clusters.

## Features
Locus is based upon the idea of organizing computation using presheaf theory. 

* support for presheaves over preorders: including the functional dependencies of relations, sets, functions, disets, bijections, difunctions, dibijections, nsets, nfunctions, nbijections, triangles, spans, cospans, diamonds, gems, chains, ditriangles, cubes, trijections, multijections, and so on.
* presheaves over monoids: MSets, GSets, and related structures.
* presheaves over free categories: concrete quiver representations
* support for presheaves over product categories: bicopresheaves, tricopresheaves, the hom functor, etc. Support for presheaves over coproduct categories and the construction of such presheaves by direct sum of simpler presheaves.
* support for a broad variety of presheaves over general categories: quivers, permutable quivers, unital quivers, dependency quivers, ternary quivers, higher arity quivers, functional quivers, compositional quivers, two quivers, n-quivers, path quivers, globular sets, simplicial sets, and presheaves over arbitrary categories.
* support for presheaves over sites: sheaves as a special case in presheaf theory
* support for modeling subalgebras using presheaves of unary relations and congruences using presheaves of setoids
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
1.5.5 release

## Contributing
Contributions are welcome.
