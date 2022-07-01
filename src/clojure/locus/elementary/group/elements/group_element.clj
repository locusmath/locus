(ns locus.elementary.group.elements.group-element
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.group.object :refer :all]))

; The category of groups is a concrete category, with forgetful set-valued functor from any group
; to its set of morphisms. Thusly, we say that a group element is synonymous with a morphism
; element of the group.

(deftype GroupElement [group elem]
  AbstractMorphism
  (source-object [this] 0)
  (target-object [this] 0)

  Invertible
  (inv [this]
    (GroupElement. group ((.inv group) elem))))

(defmethod compose* GroupElement
  [a b]

  (GroupElement.
    (.group a)
    ((.group a) (list (.elem a) (.elem b)))))

(defn group-elements
  [group]

  (set
    (map
      (fn [i]
        (GroupElement. group i))
      (underlying-set group))))
