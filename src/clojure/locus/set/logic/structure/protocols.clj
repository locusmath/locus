(ns locus.set.logic.structure.protocols
  (:require [locus.set.logic.core.set :refer :all]))

; Ontology of structured sets and functions
; We implement our computer algebra system so that objects as much as possible can be represented
; by concrete categories, with corresponding functors to the topos of Sets. This allows us to use
; the most familiar mechanisms of Sets and its arrow topos in our study of categories. In
; particular, we even represent Sets^(->) as a concrete category so that functions themselves are
; types of structured sets.

; Ontology of copresheaves
(derive :locus.set.logic.core.set/universal ::copresheaf)

(derive ::morphism-of-copresheaves ::copresheaf)
(derive ::set-function ::morphism-of-copresheaves)
(derive ::injective-set-function ::set-function)
(derive ::surjective-set-function ::set-function)
(derive ::invertible-set-function ::injective-set-function)
(derive ::invertible-set-function ::surjective-set-function)
(derive ::transformation ::set-function)
(derive ::permutation ::transformation)
(derive ::permutation ::invertible-set-function)
(derive ::inclusion-function ::injective-set-function)
(derive ::identity-function ::permutation)
(derive ::identity-function ::inclusion-function)

; Ontology of structures
(derive ::structured-set ::structure)
(derive :locus.set.logic.core.set/universal ::structured-set)
(derive ::structured-function ::structured-set)
(derive ::set-function ::structured-function)

; Ontology of elements
(derive ::function-element ::element)

; A predicate for copresheaves in general
(defn copresheaf?
  [obj]

  (isa? (type obj) ::copresheaf))

(defn morphism-of-copresheaves?
  [obj]

  (isa? (type obj) ::morphism-of-copresheaves))

; Objects in concrete categories
(defmulti structured-set? type)

(defmethod structured-set? :default
  [x] (isa? (type x) ::structured-set))

; Morphisms in concrete categories
(defmulti structured-function? type)

(defmethod structured-function? :default
  [x] (isa? (type x) ::structured-function))

; Fundamental protocols of category theory
; Categories are associated with means of describing source and target objects of morphisms.
(defprotocol AbstractMorphism
  "An abstract protocol for defining functions on morphisms of a category."

  (source-object [this]
    "Get the source object of a morphism. If f:A->B is a morphism this returns A.")
  (target-object [this]
    "Get the target object of a morphism. If f:A->B is a morphism this returns B."))

; Fundamental protocols of groupoid theory
; Groupoids are associated with a means of taking a morphism f: A -> B and associating it with an
; inverse morphism f^(-1) : B -> A which inverts the original morphism.
(defprotocol Invertible
  "A protocol for describing morphisms in groupoids. Every morphism in a groupoid
   f: A->B is associated with an inverse morphism f^{-1}: B->A such that ff^{-1}
   and f^{-1}f are both equal to the identity."

  (inv [this]
    "Produce the inverse morphism of an invertible morphism of a category."))

; Fundamental mechanisms for dealing with concrete categories
; Let C be a concrete category. Then the concreteness of this category is a consequence of two
; components (1) the concreteness of objects and (2) the concreteness of morphisms. The
; former is implemented by the ConcreteObject protocol which gives an object an underlying set
; and the latter is implemented by the ConcreteMorphism protocol in conjunction with
; the clojure.lang.IFn interface. A class implementing both interfaces can be considered
; to be a class of functions.
(defprotocol ConcreteObject
  "Let C be a concrete category. Then C is naturally associated to a forgetful functor
   of the form f: C->Sets. This forgetful functor has the data of an object function
   producing the underlying set of an object and a morphism function producing the
   underlying function of a morphism. This handles the former case."

  (underlying-set [this]
    "The underlying set of an object of a concrete category."))

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

; We also need something to deal with underlying relations
(defmulti underlying-relation type)

; The underlying multirelation is a natural generalisation of underlying relations
(defmulti underlying-multirelation type)

(defmethod underlying-multirelation :default
  [structure] (underlying-relation structure))

; Multimethods for dealing with composition and identities in categories
(defmulti identity-morphism type)

(defmulti compose*
          (fn [a b] (type a)))

(def compose
  (fn
    ([a] a)
    ([a b] (compose* a b))
    ([a b & more] (reduce compose* (compose* a b) more))))

; The size of a structure is always the size of its underlying set
(defn size
  [structure]

  (count (underlying-set structure)))

; Protocols for dealing with elements of structured sets
(defprotocol Element
  "This is a protocol for describing the elements of structured set."

  (parent [this]
    "The structured set that contains a given element."))

(defprotocol IdentifiableInstance
  "This protocol describes a mechanism for deconstructing elements of structures."

  (unwrap [this]
    "Deconstruct an element of a given structure."))

(defmulti wrap (fn [a b] (type a)))

; Multimethods for presheaf theory
(defmulti get-set (fn [a b] (type a)))

(defmulti get-function (fn [a b] (type a)))

; Multimethods for structure presheaf theory
(defmulti get-object (fn [i obj] (type i)))

(defmulti get-morphism (fn [i obj] (type i)))

; Subobjects and congruences as generalized methods for dealing with all
; kinds of different types of data structures
(defmulti subalgebra? (fn [a b] [(type a) (type b)]))

(defmulti substructure (fn [a b] [(type a) (type b)]))

(defmulti congruence? (fn [a b] [(type a) (type b)]))

(defmulti quotient (fn [a b] [(type a) (type b)]))


