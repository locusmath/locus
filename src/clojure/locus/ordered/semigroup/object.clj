(ns locus.ordered.semigroup.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.sr :refer [complete-relation]]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.order.general.core.object :refer :all]))

; A preordered semigroup is a 2-semigroupoid in which the 2-quiver of 2-morphisms between
; 1-morphisms is always thin. This is a direct generalisation of a locally ordered
; category which is a type of 2-category, which doesn't require the existence of identities.
; The general case of preordered semigroups is included because of its importance in a number
; of fields such as commutative semigroup theory. Every commutative semigroup is naturally
; preordered by its Green's preorders.

(deftype PreorderedSemigroup [elems order op]
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

(derive PreorderedSemigroup :locus.set.copresheaf.structure.core.protocols/semigroup)

; Breakdown of preordered semigroups
(defmethod underlying-semigroup PreorderedSemigroup
  [^PreorderedSemigroup semigroup]

  (.-op semigroup))

(defmethod underlying-preorder PreorderedSemigroup
  [^PreorderedSemigroup semigroup]

  (.-order semigroup))

; Underlying relations of preordered semigroups are defined by their underlying quivers
(defmethod underlying-multirelation PreorderedSemigroup
  [^PreorderedSemigroup semigroup] (underlying-multirelation (underlying-quiver semigroup)))

(defmethod underlying-relation PreorderedSemigroup
  [^PreorderedSemigroup semigroup] (underlying-relation (underlying-quiver semigroup)))

; Constructors for special types of ordered semigroups
(defn discrete-semigroup
  [semigroup]

  (->PreorderedSemigroup
    (morphisms semigroup)
    (discrete-preorder (morphisms semigroup))
    semigroup))

(defn indiscrete-semigroup
  [semigroup]

  (->PreorderedSemigroup
    (morphisms semigroup)
    (complete-preposet (morphisms semigroup))
    semigroup))

; Let S be a commutative semigroup. Then all Green's preorders on S coincide, and they form a single
; preorder on S called the algebraic preorder. This then forms a preorder on S which also turns
; it into a preordered semigroup, because the composition of S is monotone on its own Green's
; J preorder by commutativity. Using this property, we can naturally treat all commutative
; semigroups as if they are ordered algebraic structures.
(defn naturally-preorded-commutative-semigroup
  [semigroup]

  (->PreorderedSemigroup
    (morphisms semigroup)
    (to-preposet (jpreorder semigroup))
    semigroup))

; Ontology of preordered semigroups
; In the classification of preordered semigroups we can classify preordered semigroups either by
; their underlying preorders or by their underlying semigroups. In addition to these sorts
; of classifications there are more advanced classifications which deal with the relationship
; between semigropus and their orderings. Altogether these classes make up our ontology of
; preordered semigroups.
(defn preordered-semigroup?
  [semigroup]

  (= (type semigroup) PreorderedSemigroup))

(defn preordered-monoid?
  [semigroup]

  (and
    (preordered-semigroup? semigroup)
    (monoid? (underlying-semigroup semigroup))))

(defn ordered-semigroup?
  [semigroup]

  (and
    (preordered-semigroup? semigroup)
    (skeletal-thin-category? (underlying-preorder semigroup))))

(defn ordered-monoid?
  [monoid]

  (and
    (preordered-semigroup? monoid)
    (monoid? (underlying-semigroup monoid))
    (skeletal-thin-category? (underlying-preorder monoid))))

(defn discrete-semigroup?
  [semigroup]

  (and
    (preordered-semigroup? semigroup)
    (discrete-category? (underlying-preorder semigroup))))

(defn indiscrete-semigroup?
  [semigroup]

  (and
    (preordered-semigroup? semigroup)
    (complete-thin-groupoid? (underlying-preorder semigroup))))

(defn discrete-monoid?
  [semigroup]

  (and
    (preordered-semigroup? semigroup)
    (monoid? (underlying-semigroup semigroup))
    (discrete-category? (underlying-preorder semigroup))))

(defn indiscrete-monoid?
  [semigroup]

  (and
    (preordered-semigroup? semigroup)
    (monoid? (underlying-semigroup semigroup))
    (complete-thin-groupoid? (underlying-preorder semigroup))))

