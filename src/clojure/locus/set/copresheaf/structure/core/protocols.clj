(ns locus.set.copresheaf.structure.core.protocols
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; Ontology of actions
(derive ::mset :locus.set.logic.structure.protocols/structured-set)
(derive ::equivariant-map :locus.set.logic.structure.protocols/structured-function)

; Ontology of structured quivers
(derive ::structured-unital-quiver :locus.set.quiver.structure.core.protocols/structured-quiver)
(derive ::structured-permutable-quiver :locus.set.quiver.structure.core.protocols/structured-quiver)
(derive ::structured-dependency-quiver ::structured-unital-quiver)
(derive ::structured-dependency-quiver ::structured-permutable-quiver)

; Ontology of morphisms of structured quivers
(derive ::morphism-of-structured-unital-quivers :locus.set.quiver.structure.core.protocols/morphism-of-structured-quivers)
(derive ::morphism-of-structured-permutable-quivers ::morphism-of-structured-quivers)
(derive ::morphism-of-structured-dependency-quivers ::morphism-of-structured-unital-quivers)
(derive ::morphism-of-structured-dependency-quivers ::morphism-of-structured-permutable-quivers)

; Ontology of compositional quivers
(derive ::structured-partial-magmoid :locus.set.quiver.structure.core.protocols/structured-quiver)
(derive ::structured-magmoid ::structured-partial-magmoid)
(derive ::structured-semigroupoid ::structured-magmoid)
(derive ::structured-category ::structured-semigroupoid)
(derive ::structured-category ::structured-unital-quiver)

(derive ::partial-magmoid ::structured-partial-magmoid)
(derive ::magmoid ::structured-magmoid)
(derive ::semigroupoid ::structured-semigroupoid)
(derive ::category ::structured-category)
(derive ::groupoid ::structured-dependency-quiver)

(derive ::magmoid ::partial-magmoid)
(derive ::thin-partial-magmoid ::partial-magmoid)
(derive ::thin-semigroupoid ::thin-partial-magmoid)
(derive ::partial-magma ::partial-magmoid)
(derive ::magma ::partial-magma)
(derive ::partial-semigroup ::partial-magma)
(derive ::semigroup ::partial-semigroup)

(derive ::semigroupoid ::magmoid)
(derive ::category ::semigroupoid)
(derive ::groupoid ::category)

(derive ::magma ::magmoid)
(derive ::semigroup ::semigroupoid)
(derive ::semigroup ::magma)
(derive ::monoid ::category)
(derive ::monoid ::semigroup)
(derive ::group ::groupoid)
(derive ::group ::monoid)
(derive ::group-with-zero ::monoid)

(derive ::commutative-semigroup ::semigroup)
(derive ::commutative-monoid ::monoid)
(derive ::commutative-monoid ::commutative-semigroup)
(derive ::commutative-group ::group)
(derive ::commutative-group ::commutative-monoid)
(derive ::commutative-group-with-zero ::group-with-zero)
(derive ::commutative-group-with-zero ::commutative-monoid)

(derive ::thin-semigroupoid ::semigroupoid)
(derive ::thin-category ::thin-semigroupoid)
(derive ::thin-category ::category)

(derive ::thin-groupoid ::groupoid)
(derive ::thin-groupoid ::thin-category)
(derive ::thin-skeletal-category ::thin-category)
(derive ::lattice ::thin-skeletal-category)

; Concrete compositional quivers
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

; Ontology of morphisms of compositional quivers
(derive ::partial-magmoid-homomorphism :locus.set.quiver.structure.core.protocols/morphism-of-structured-quivers)
(derive ::magmoid-homomorphism ::partial-magmoid-homomorphism)
(derive ::partial-magma-homomorphism ::partial-magmoid-homomorphism)
(derive ::magma-homomorphism ::partial-magma-homomorphism)

(derive ::semigroup-homomorphism ::magma-homomorphism)
(derive ::semifunctor ::magmoid-homomorphism)

(derive ::functor ::semifunctor)
(derive ::functor ::morphism-of-structured-unital-quivers)

(derive ::monotone-map ::functor)

(derive ::groupoid-functor ::functor)
(derive ::groupoid-functor ::morphism-of-structured-dependency-quivers)

(derive ::semigroup-homomorphism ::semifunctor)
(derive ::monoid-homomorphism ::semigroup-homomorphism)
(derive ::monoid-homomorphism ::functor)
(derive ::group-homomorphism ::monoid-homomorphism)
(derive ::group-homomorphism ::groupoid-functor)

; Ontology of structure copresheaves
(derive ::bicopresheaf ::structure-copresheaf)

; Structured bijections
(derive ::structured-bijection :locus.set.logic.structure.protocols/structured-function)
(derive ::bijection ::structured-bijection)
(derive ::gem ::structured-difunction)

; Protocols related to structured bijections
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

; For now we are going to need to have a generalized inverse function for groupoids
(defmulti inverse-function type)

; Adjoin composition to various types of quivers
(defmulti adjoin-composition (fn [quiv f] (type quiv)))

; The paths of a category include all elements of its composition domain
(defmethod paths :locus.set.copresheaf.structure.core.protocols/partial-magmoid
  [magmoid] (inputs magmoid))

; The ontology of categories comes in two parts: firstly we have an ontology of categories
; which we can construct using Clojure's makeshift hierarchy system. Secondly, we can
; construct an ontology of categories corresponding to classes and predicates and the
; inclusions between them. The former is necessary in order to define generic methods that
; can more effectively operate on different classes of categories and semigroupoids.
(defmulti structured-unital-quiver? type)

(defmethod structured-unital-quiver? :default
  [x] (isa? (type x) ::structured-unital-quiver))

(defmulti structured-permutable-quiver? type)

(defmethod structured-permutable-quiver? :default
  [x] (isa? (type x) ::structured-permutable-quiver))

(defmulti structured-dependency-quiver? type)

(defmethod structured-dependency-quiver? :default
  [x] (isa? (type x) ::structured-dependency-quiver))

; Ontology of compositional quivers
(defmulti partial-magmoid? type)

(defmethod partial-magmoid? ::partial-magmoid
  [obj] true)

(defmethod partial-magmoid? :default
  [obj] false)

(defmulti magmoid? type)

(defmethod magmoid? ::magmoid
  [obj] true)

(defmethod magmoid? :default
  [obj] false)

(defmulti semigroupoid? type)

(defmethod semigroupoid? ::semigroupoid
  [obj] true)

(defmethod semigroupoid? :default
  [obj] false)

(defmulti category? type)

(defmethod category? ::category
  [x] true)

(defmethod category? :default
  [x] false)

(defmulti groupoid? type)

(defmethod groupoid? :default
  [x] (isa? (type x) ::groupoid))

(defmulti concrete-category? type)

(defmethod concrete-category? :default
  [x] (isa? (type x) ::category))

(defmulti thin-partial-magmoid? type)

(defmethod thin-partial-magmoid? :default
  [x] (isa? (type x) ::thin-partial-magmoid))

(defmulti thin-semigroupoid? type)

(defmethod thin-semigroupoid? :default
  [x] (isa? (type x) ::thin-semigroupoid))

(defmulti thin-category? type)

(defmethod thin-category? :default
  [x] (isa? (type x) ::thin-category))

(defmulti thin-groupoid? type)

(defmethod thin-groupoid? :default
  [x] (isa? (type x) ::thin-groupoid))

(defmulti lattice? type)

(defmethod lattice? :default
  [x] (isa? (type x) ::lattice))

; In addition to our basic ontology of categories and groupoids, we need to construct
; an additional ontology of functors, semifunctors, and groupoid homomorphisms. These
; are morphisms in the corresponding categories of structures.
(defmulti partial-magmoid-homomorphism? type)

(defmethod partial-magmoid-homomorphism? :default
  [x] (isa? (type x) ::partial-magmoid-homomorphism))

(defmulti magmoid-homomorphism? type)

(defmethod magmoid-homomorphism? :default
  [x] (isa? (type x) ::magmoid-homomorphism))

(defmulti semifunctor? type)

(defmethod semifunctor? :default
  [x] (isa? (type x) ::semifunctor))

(defmulti functor? type)

(defmethod functor? :default
  [x] (isa? (type x) ::functor))

(defmulti groupoid-functor? type)

(defmethod groupoid-functor? :default
  [x] (isa? (type x) ::groupoid-functor))

; Index categories of copresheaves
(defmulti index type)

; Index categories for multifunctors
(defmulti index-multiplicands type)

(defmethod index-multiplicands :default
  [functor] (list (index functor)))

; Underlying preorders and semigroups
(defmulti underlying-preorder type)

(defmethod underlying-preorder ::thin-category
  [category] category)

(defmulti underlying-semigroup type)

(defmethod underlying-semigroup ::semigroup
  [semigroup] semigroup)

; Elements of higher categories and higher quivers
(defmulti k-morphisms (fn [quiver i] (type quiver)))

(defmethod k-morphisms :locus.set.quiver.structure.core.protocols/structured-nary-quiver
  [quiver i]

  (case i
    0 (objects quiver)
    1 (morphisms quiver)))

; Heights for higher quivers and higher categories
(defmulti quiver-height type)

(defmethod quiver-height :locus.set.quiver.structure.core.protocols/nary-quiver
  [quiver] 2)

; Display tables
(defmethod display-table ::partial-magmoid
  [magmoid]

  (display-table (underlying-function magmoid)))

; Algebraic preorders for naturally preordered algebraic structures
(defmulti natural-preorder type)

; Identity elements and zero elements of semigroups
(defmulti identity-elements type)

(defmulti zero-elements type)

(defmulti adjoin-zero type)

(defmulti adjoin-identity type)
