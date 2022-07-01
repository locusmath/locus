(ns locus.elementary.function.core.protocols
  (:require [locus.elementary.relation.binary.product :refer :all]))

; This file provides generic methods for dealing with categories and topoi. In particular,
; we define a makeshift hierarchy of symbols for use with Clojure's multimethods.

; Fundamental protocols of category theory
(defprotocol AbstractMorphism
  "An abstract protocol for defining functions on morphisms of a category."

  (source-object [this]
    "Get the source object of a morphism. If f:A->B is a morphism this returns A.")
  (target-object [this]
    "Get the target object of a morphism. If f:A->B is a morphism this returns B."))

(defprotocol Invertible
  "A protocol for describing morphisms of groupoids. Every morphism of a groupoid
   f: A->B is associated with an inverse morphism f^{-1}: B->A such that ff^{-1}
   and f^{-1}f are both equal to the identity."

  (inv [this]
    "Produce the inverse morphism of an invertible morphism of a category."))

(defprotocol ConcreteObject
  "Let C be a concrete category. Then C is naturally associated to a forgetful functor
   of the form f: C->Sets. This forgetful functor has the data of an object function
   producing the underlying set of an object and a morphism function producing the
   underlying function of a morphism. This handles the former case."

  (underlying-set [this]
    "The underlying set of an object of a concrete category."))

; Structured set pairs, functions, and bijections
; There are three types of preorders on two elements: an empty two element preorder,
; an arrow preorder, and the symmetric preorder of two objects and two arrows going
; back and forth between them. These three fundamental preorders correspond to
; three of the most fundamental topoi: the topoi of pairs of sets, functions, and of
; bijections which together play a fundamental role in topos theoretic foundations.
(defprotocol ConcreteMorphism
  "Let C be a concrete category. Then C is naturally asssociated to a forgetful functor
  of the form f:C->Sets. Suppose that m : A to B is a morphism, then f(m) : f(A) -> f(B)
  is a function. This protocol defines the inputs set f(A) and the outputs set f(B)
  of a concrete morphism. The final conversion of a morphism of a concrete category in
  to a function is handled by combination with clojure.lang.IFn."

  (inputs [this]
    "The input set of a morphism of a concrete category.")
  (outputs [this]
    "The output set of a morphism of a concrete category."))

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
(defprotocol ConcreteCategoricalStructure
  "While concrete object and morphism protocols handle the elements of a concrete category,
  this protocol handles concrete categories themselves. This requires the data of a forgetful
  functor from the category to the topos Sets. This forgetful functor can be defined by
  a pair of functions mapping objects to sets and morphisms to functions."

  (object-to-set [this object]
    "Map an object of a concrete category to a set.")
  (morphism-to-function [this morphism]
    "Map a morphism of a concrete category to a function."))

; A hierarchy of structured quivers
(derive ::semigroupoid ::structured-quiver)
(derive ::category ::semigroupoid)
(derive ::groupoid ::category)
(derive ::semigroup ::semigroupoid)
(derive ::monoid ::semigroup)
(derive ::monoid ::category)
(derive ::group ::groupoid)
(derive ::group ::monoid)
(derive ::thin-semigroupoid ::semigroupoid)
(derive ::thin-category ::category)
(derive ::thin-category ::thin-semigroupoid)
(derive ::thin-groupoid ::groupoid)
(derive ::thin-groupoid ::thin-category)
(derive ::lattice ::thin-category)
(derive ::concrete-category ::category)

; A corresponding hierarchy of morphisms of structured quivers
(derive ::semifunctor ::morphism-of-structured-quivers)
(derive ::functor ::semifunctor)
(derive ::groupoid-functor ::functor)
(derive ::semigroup-homomorphism ::semifunctor)
(derive ::monoid-homomorphism ::semigroup-homomorphism)
(derive ::monoid-homomorphism ::functor)
(derive ::group-homomorphism ::monoid-homomorphism)
(derive ::group-homomorphism ::groupoid-functor)

; Hierarchy of structured sets
(derive ::semigroup ::structured-set)
(derive ::thin-category ::structured-set)

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

; We also need something to deal with underlying relations
(defmulti underlying-relation type)

; The underlying multirelation is a natural generalisation of underlying relations
(defmulti underlying-multirelation type)

; Multimethods for dealing with composition and identities in categories
(defmulti identity-morphism type)

(defmulti compose*
          (fn [a b] (type a)))

(def compose
  (fn
    ([a] a)
    ([a b] (compose* a b))
    ([a b & more] (reduce compose* (compose* a b) more))))

; Multimethods for dealing with products and coproducts in categories
(defmulti product
          (fn [& args] (type (first args))))

(defmethod product :default
  [& args]

  (apply cartesian-product args))

(defmulti coproduct
          (fn [& args] (type (first args))))

(defmethod coproduct :default
  [& args]

  (apply cartesian-coproduct args))

; Get the dual of a category, semigroup, etc
(defmulti dual type)

; For now we are going to need to have a generalized inverse function for groupoids
(defmulti inverse-function type)

; Adjoin composition to various types of quivers
(defmulti adjoin-composition (fn [quiv f] (type quiv)))

; The ontology of categories comes in two parts: firstly we have an ontology of categories
; which we can construct using Clojure's makeshift hierarchy system. Secondly, we can
; construct an ontology of categories corresponding to classes and predicates and the
; inclusions between them. The former is necessary in order to define generic methods that
; can more effectively operate on different classes of categories and semigroupoids.
(defmulti structured-quiver? type)

(defmethod structured-quiver? :default
  [x] (isa? (type x) ::structured-quiver))

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
(defmulti semifunctor? type)

(defmethod semifunctor? :default
  [x] (isa? (type x) ::semifunctor))

(defmulti functor? type)

(defmethod functor? :default
  [x] (isa? (type x) ::functor))

(defmulti groupoid-functor? type)

(defmethod groupoid-functor? :default
  [x] (isa? (type x) ::groupoid-functor))

; Structured sets
(defmulti structured-set? type)

(defmethod structured-set? :default
  [x] (isa? (type x) ::structured-set))

; Ontology of morphisms in the topos of functions
(derive ::inclusion-function ::set-function)
(derive ::identity-function ::inclusion-function)


