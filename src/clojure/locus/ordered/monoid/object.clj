(ns locus.ordered.monoid.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.sr :refer [complete-relation]]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.commutative.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.order.general.core.object :refer :all])
  (:import (locus.algebra.commutative.monoid.object CommutativeMonoid)))

; A preordered monoid is a 2-category that is simultaneously a locally preordered category and
; a monoidal category. Every preordered monoid can be divided by its symmetric components to
; get an ordered monoid. Every commutative monoid is a naturally preordered monoid, where
; the natural preorder is given by Green's J preorder, which coincides with all other Green's
; preorders in the commutative case. Then the commutative monoid can be condensed to get a
; partially ordered commutative J-trivial monoid, just as any preordered monoid can be
; condensed to a partially ordered monoid.

(deftype PreorderedMonoid [elems order op]
  ConcreteObject
  (underlying-set [this] elems)

  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PreorderedMonoid :locus.set.copresheaf.structure.core.protocols/monoid)

; Breakdown of preordered monoids
(defmethod underlying-semigroup PreorderedMonoid
  [^PreorderedMonoid monoid]

  (.-op monoid))

(defmethod underlying-preorder PreorderedMonoid
  [^PreorderedMonoid monoid]

  (.-order monoid))

; Underlying relations of preordered monoids are defined by their underlying quivers
(defmethod underlying-multirelation PreorderedMonoid
  [^PreorderedMonoid monoid] (underlying-multirelation (underlying-quiver monoid)))

(defmethod underlying-relation PreorderedMonoid
  [^PreorderedMonoid monoid] (underlying-relation (underlying-quiver monoid)))

(defmethod identity-elements PreorderedMonoid
  [^PreorderedMonoid monoid] (identity-elements (underlying-semigroup monoid)))

; Constructors for special types of ordered monoids
(defn discrete-monoid
  [semigroup]

  (->PreorderedMonoid
    (morphisms semigroup)
    (discrete-preorder (morphisms semigroup))
    semigroup))

(defn indiscrete-monoid
  [semigroup]

  (->PreorderedMonoid
    (morphisms semigroup)
    (complete-preposet (morphisms semigroup))
    semigroup))

; Let S be a commutative monoid. Then all Green's preorders on S coincide, and they form a single
; preorder on S called the algebraic preorder. This then forms a preorder on S which also turns
; it into a preordered monoid, because the composition of S is monotone on its own Green's
; J preorder by commutativity. Using this property, we can naturally treat all commutative
; monoid as if they are ordered algebraic structures.
(defn naturally-preordered-commutative-monoid
  [semigroup]

  (->PreorderedMonoid
    (morphisms semigroup)
    (to-preposet (jpreorder semigroup))
    semigroup))

; Conversion routines for preordered monoids
(defmulti to-preordered-monoid type)

(defmethod to-preordered-monoid PreorderedMonoid
  [^PreorderedMonoid monoid] monoid)

(defmethod to-preordered-monoid CommutativeMonoid
  [monoid] (naturally-preordered-commutative-monoid monoid))

; Ontology of preordered monoids
; In the classification of preordered monoids we can classify preordered monoids either by
; their underlying preorders or by their underlying monoids. In addition to these sorts
; of classifications there are more advanced classifications which deal with the relationship
; between monoids and their orderings. Altogether these classes make up our ontology of
; preordered monoids.
(defn preordered-monoid?
  [monoid]

  (= (type monoid) PreorderedMonoid))

(defn ordered-monoid?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (skeletal-thin-category? (underlying-preorder monoid))))

(defn discrete-monoid?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (discrete-category? (underlying-preorder monoid))))

(defn indiscrete-monoid?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (complete-thin-groupoid? (underlying-preorder monoid))))

(defn preordered-commutative-monoid?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (commutative-monoid? (underlying-semigroup monoid))))

(defn ordered-commutative-monoid?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (skeletal-thin-category? (underlying-preorder monoid))
    (commutative-monoid? (underlying-semigroup monoid))))

(defn preordered-group?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (group? (underlying-semigroup monoid))))

(defn ordered-group?
  [monoid]

  (and
    (preordered-monoid? monoid)
    (group? (underlying-semigroup monoid))
    (skeletal-thin-category? (underlying-preorder monoid))))
