(ns locus.elementary.semigroup.elements.semigroup-element
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]))

; The category of semigroups is a concrete category. The Set-valued functor of the category of semigroups
; maps any given semigroup to its class of morphisms. Therefore, we can refer to the morphisms of a semigroup
; as the elements of a semigroup. We define these morphisms by the semigroup element class.

(deftype SemigroupElement [semigroup elem]
  AbstractMorphism
  (source-object [this] 0)
  (target-object [this] 0))

(defmethod compose* SemigroupElement
  [a b]

  (SemigroupElement.
    (.semigroup a)
    ((.semigroup a) (list (.elem a) (.elem b)))))

(defn semigroup-elements
  [semigroup]

  (set
    (map
      (fn [i]
        (SemigroupElement. semigroup i))
      (underlying-set semigroup))))

