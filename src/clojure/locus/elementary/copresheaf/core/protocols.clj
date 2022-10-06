(ns locus.elementary.copresheaf.core.protocols
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; Ontology of structured copresheaves
; Every single object in our ontology can be considered in terms of some kind of underlying
; copresheaf: such as a set, diset, function, or difunction.

; Ontology of structured sets
(derive ::mset :locus.base.logic.structure.protocols/structured-set)

; Ontology of structured disets
(derive ::structured-diset :locus.base.logic.structure.protocols/structured-set)
(derive ::diset ::structured-diset)

; Ontology of structured functions
(derive :locus.base.logic.structure.protocols/structured-function ::structured-diset)
(derive ::equivariant-map :locus.base.logic.structure.protocols/structured-function)

; Ontology of structured bijections
(derive ::structured-bijection :locus.base.logic.structure.protocols/structured-function)
(derive ::bijection ::structured-bijection)

; Ontology of structured quivers
(derive ::ternary-quiver ::structured-diset)
(derive ::thin-ternary-quiver ::ternary-quiver)
(derive ::at-quiver ::thin-ternary-quiver)

(derive ::structured-quiver ::structured-diset)
(derive ::structured-unital-quiver ::structured-quiver)
(derive ::structured-permutable-quiver ::structured-quiver)
(derive ::structured-dependency-quiver ::structured-unital-quiver)
(derive ::structured-dependency-quiver ::structured-permutable-quiver)

(derive ::structured-semigroupoid ::structured-quiver)
(derive ::structured-category ::structured-semigroupoid)
(derive ::structured-category ::structured-unital-quiver)
(derive ::structured-groupoid ::structured-category)
(derive ::structured-groupoid ::structured-dependency-quiver)

(derive ::semigroupoid ::structured-semigroupoid)
(derive ::category ::structured-category)
(derive ::groupoid ::structured-groupoid)
(derive ::category ::semigroupoid)
(derive ::groupoid ::category)

(derive ::semigroup ::semigroupoid)
(derive ::monoid ::semigroup)
(derive ::monoid ::category)
(derive ::group ::groupoid)
(derive ::group ::monoid)

(derive ::group-with-zero ::monoid)

(derive ::thin-semigroupoid ::semigroupoid)
(derive ::thin-category ::thin-semigroupoid)
(derive ::thin-category ::category)
(derive ::thin-groupoid ::groupoid)
(derive ::thin-groupoid ::thin-category)

(derive ::thin-skeletal-category ::thin-category)
(derive ::lattice ::thin-skeletal-category)

(derive ::concrete-semigroupoid ::semigroupoid)
(derive ::concrete-category ::category)
(derive ::concrete-groupoid ::groupoid)
(derive ::concrete-semigroup ::semigroup)
(derive ::concrete-monoid ::monoid)
(derive ::concrete-group ::group)

(derive ::concrete-category ::concrete-semigroupoid)
(derive ::concrete-groupoid ::concrete-category)
(derive ::concrete-semigroup ::concrete-semigroupoid)
(derive ::concrete-monoid ::concrete-semigroup)
(derive ::concrete-monoid ::concrete-category)
(derive ::concrete-group ::concrete-monoid)
(derive ::concrete-group ::concrete-groupoid)

; Ontology of structured difunctions
(derive ::structured-difunction :locus.base.logic.structure.protocols/structured-function)
(derive ::difunction ::structured-difunction)

(derive ::diamond ::structured-difunction)
(derive ::gem ::structured-difunction)

(derive ::morphism-of-structured-quivers ::structured-difunction)
(derive ::morphism-of-structured-unital-quivers ::morphism-of-structured-quivers)
(derive ::morphism-of-structured-permutable-quivers ::morphism-of-structured-quivers)
(derive ::morphism-of-structured-dependency-quivers ::morphism-of-structured-unital-quivers)
(derive ::morphism-of-structured-dependency-quivers ::morphism-of-structured-permutable-quivers)

(derive ::semifunctor ::morphism-of-structured-quivers)
(derive ::functor ::semifunctor)
(derive ::functor ::morphism-of-structured-unital-quivers)
(derive ::groupoid-functor ::functor)
(derive ::groupoid-functor ::morphism-of-structured-dependency-quivers)

(derive ::semigroup-homomorphism ::semifunctor)
(derive ::monoid-homomorphism ::semigroup-homomorphism)
(derive ::monoid-homomorphism ::functor)
(derive ::group-homomorphism ::monoid-homomorphism)
(derive ::group-homomorphism ::groupoid-functor)

; Structured copresheaves in topos theory
; Structured pairs of sets, bijections, pairs of functions, pairs of bijections, morphisms
; of functions and morphisms of bijections.
(defprotocol ConcreteHigherMorphism
  "Topos theoretic foundations often lead us to treat functions as objects in their own
  right. Further, we often have categories that are often a lot like categorise with additional
  structure. Corresponding to this, we generalize from categories of structured sets to categories
  of structured functions and we generalize from underlying functions to underlying morphisms
  of functions in the arrow topos of the topos of Sets."

  (underlying-morphism-of-functions [this]
    "Map a morphism of a category into a morphism in the topos of functions."))

(defprotocol StructuredDiset
  "The topos of pairs of sets Sets^2 is one of the most basic and fundamental of topoi
  studied in elementary topos theory. Consequently, there are a number of more advanced
  structures that are constructed over Sets^2, which require forgetful functors to it.
  Small categories themselves are a case in point, where the two sets are simply the
  object set and the morphism set of the category."

  (first-set [this]
    "The first set of the mapping of an object to the topos Sets^2.")
  (second-set [this]
    "The second set of the mapping of an object to the topos Sets^2."))

(defprotocol StructuredDifunction
  "This is the morphism part of a functor from a category into the topos Sets^2. It
   it is simply defined by taking a morphism and producing the pair of functions
   that define a morphism in the topos Sets^2."

  (first-function [this]
    "The first function in the mapping of a morphism to the topos Sets^2.")
  (second-function [this]
    "The second function in the mapping of a morphism to the topos Sets^2."))

(defprotocol StructuredDibijection
  "A dibijection is a pair of bijections, which can be considered to be an object
  in the topos Sets^{K_2 + K_2} or an isomorphism in the topos Sets^2. In either
  case, it is defined by an object that implements an interface defining accessors
  for the two bijections in the structured pair of bijections."

  (first-bijection [this]
    "The first bijection in a structured pair of bijections.")
  (second-bijection [this]
    "The second bijection in a structured pair of bijections."))

(defprotocol StructuredBijection
  "A bijection is an object of the topos Sets^{K2} where K2 is the thin category
  consisting of two objects and four morphisms. The structured bijection protocol
  defines mappings of objects into this topos."

  (underlying-bijection [this]
    "The underlying bijection of a structured bijection."))

(defprotocol StructuredBijectionMorphism
  "A morphism in the topos of bijections is similar in almost everyway to a morphism
  in the topos of functions, but they have a special data type associated to them,
  and so this protocol corresponds to the bijection morphism data type for morphisms
  in categories structured over the topos of bijections."

  (underlying-morphism-of-bijections [this]
    "Map a morphism in a category to a morphism in the topos of bijections."))

; Concrete categories
; Concrete categories must have special methods for dealing with the conversion of objects
; and morphisms to members of the topos Sets.
(defprotocol ConcreteCategoricalStructure
  "While concrete object and morphism protocols handle the elements of a concrete category,
  this protocol handles concrete categories themselves. This requires the data of a forgetful
  functor from the category to the topos Sets. This forgetful functor can be defined by
  a pair of functions mapping objects to sets and morphisms to functions."

  (object-to-set [this object]
    "Map an object of a concrete category to a set.")
  (morphism-to-function [this morphism]
    "Map a morphism of a concrete category to a function."))

; Set functions
(extend-type SetFunction
  StructuredDiset
  (first-set [this] (inputs this))
  (second-set [this] (outputs this)))

; Multimethods for category theory
; Morphisms and objects can be defined in terms of the mapping to the topos Sets^2 but in
; this case it is far more convenient to have shorthands like morphisms and objects then
; as opposed to having to use first set and second set in every case.
(defn morphisms
  [quiv] (first-set quiv))

(defn objects
  [quiv] (second-set quiv))

; Let C be a category, then C is naturally associated with some generating set of morphisms
; upon which all the morphisms of C can be described. In particular, in order to define a copresheaf
; over C it is sufficient to define it first over its generating set. An example of in action is
; the special case of finitely presented monoids. In order to make it so that every category has
; a canonical generating set, we default to the condition that the set of all morphisms is a
; generating set for the morphisms of a category. It follows that we don't necessarily ensure
; that the morphic generating set is minimal.
(defmulti morphic-gens type)

(defmethod morphic-gens :default
  [x] (morphisms x))

(defn number-of-generators
  [x] (count (morphic-gens x)))

; Get the dual of a category, semigroup, etc
(defmulti dual type)

; For now we are going to need to have a generalized inverse function for groupoids
(defmulti inverse-function type)

; Adjoin composition to various types of quivers
(defmulti adjoin-composition (fn [quiv f] (type quiv)))

; Structured disets
(defmulti structured-diset? type)

(defmethod structured-diset? :default
  [x] (isa? (type x) ::structured-diset))

; The ontology of categories comes in two parts: firstly we have an ontology of categories
; which we can construct using Clojure's makeshift hierarchy system. Secondly, we can
; construct an ontology of categories corresponding to classes and predicates and the
; inclusions between them. The former is necessary in order to define generic methods that
; can more effectively operate on different classes of categories and semigroupoids.
(defmulti structured-quiver? type)

(defmethod structured-quiver? :default
  [x] (isa? (type x) ::structured-quiver))

(defmulti structured-unital-quiver? type)

(defmethod structured-unital-quiver? :default
  [x] (isa? (type x) ::structured-unital-quiver))

(defmulti structured-permutable-quiver? type)

(defmethod structured-permutable-quiver? :default
  [x] (isa? (type x) ::structured-permutable-quiver))

(defmulti structured-dependency-quiver? type)

(defmethod structured-dependency-quiver? :default
  [x] (isa? (type x) ::structured-dependency-quiver))

; Structured semigroupoids
(defmulti lattice? type)

(defmethod lattice? :default
  [x] (isa? (type x) ::lattice))

(defmulti thin-category? type)

(defmethod thin-category? :default
  [x] (isa? (type x) ::thin-category))

(defmulti thin-groupoid? type)

(defmethod thin-groupoid? :default
  [x] (isa? (type x) ::thin-groupoid))

(defmulti semigroupoid? type)

(defmethod semigroupoid? :default
  [x] (isa? (type x) ::semigroupoid))

(defmulti category? type)

(defmethod category? :default
  [x] (isa? (type x) ::category))

(defmulti groupoid? type)

(defmethod groupoid? :default
  [x] (isa? (type x) ::groupoid))

(defmulti concrete-category? type)

(defmethod concrete-category? :default
  [x] (isa? (type x) ::category))

; In addition to our basic ontology of categories and groupoids, we need to construct
; an additional ontology of functors, semifunctors, and groupoid homomorphisms. These
; are morphisms in the corresponding categories of structures.
(defmulti structured-difunction? type)

(defmethod structured-difunction? :default
  [x] (isa? (type x) ::structured-difunction))

(defmulti semifunctor? type)

(defmethod semifunctor? :default
  [x] (isa? (type x) ::semifunctor))

(defmulti functor? type)

(defmethod functor? :default
  [x] (isa? (type x) ::functor))

(defmulti groupoid-functor? type)

(defmethod groupoid-functor? :default
  [x] (isa? (type x) ::groupoid-functor))

; Section elements of copresheaves
; Let F : C -> Sets be a copresheaf. Then a section of F is a pair of an object X of C and a member
; of the set F(X). The sections of a copresheaf are the elements of their underlying set, in our
; interpretation which takes copresheaves to be members of concrete topoi.
(defprotocol SectionElement
  (tag [this])
  (member [this]))

; Generate copresheaf data that can be used for visualisation routines
(defn generate-copresheaf-data
  [object-family morphism-triples]

  (list
    object-family
    (apply
      union
      (map
        (fn [[s t func]]
          (set
            (map
              (fn [input]
                (list
                  (list s input)
                  (list t (func input))))
              (inputs func))))
        morphism-triples))))

; General mechanisms for copresheaves and other functors to be used in category theory
(defn object-apply
  [functor obj]

  ((second-function functor) obj))

(defn morphism-apply
  [functor morphism]

  ((first-function functor) morphism))

; Relational theory of dependency copresheaves
(defn relation-transition-map
  [rel i j]

  (loop [current-map {}
         current-in #{}
         current-out #{}
         current-rel (seq rel)]
    (if (empty? current-rel)
      (->SetFunction
        current-in
        current-out
        current-map)
      (let [current-element (first current-rel)
            a (nth current-element i)
            b (nth current-element j)]
        (recur
          (conj current-map [a b])
          (conj current-in a)
          (conj current-out b)
          (rest current-rel))))))

; Display tables of semigroups, magmas, partial magmas, groups, categories, semicategories,
; groupoids, magmoids, or any other table like algebraic structure.
(defmulti display-table type)