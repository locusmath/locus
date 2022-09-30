(ns locus.elementary.group.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]))

; The category of groups is a concrete category, with forgetful set-valued functor from any group
; to its set of morphisms. Thusly, we say that a group element is synonymous with a morphism
; element of the group.
(deftype GroupElement [group elem]
  Element
  (parent [this] group)

  SectionElement
  (tag [this] 0)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this] elem)

  AbstractMorphism
  (source-object [this] 0)
  (target-object [this] 0)

  Invertible
  (inv [this]
    (GroupElement. group ((.inv group) elem))))

(derive GroupElement :locus.base.logic.structure.protocols/element)

(defmethod wrap :locus.elementary.copresheaf.core.protocols/group
  [group elem]

  (->GroupElement group elem))

; Methods to be applied to group elements
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

; Ontology of group elements
(defn group-element?
  [elem]

  (= (type elem) GroupElement))