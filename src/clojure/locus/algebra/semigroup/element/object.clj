(ns locus.algebra.semigroup.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.semigroup.core.object Semigroup)))

; The category of semigroups is a concrete category. The Set-valued functor of the category of semigroups
; maps any given semigroup to its class of morphisms. Therefore, we can refer to the morphisms of a semigroup
; as the elements of a semigroup. We define these morphisms by the semigroup element class.
(deftype SemigroupElement [semigroup elem]
  Element
  (parent [this] semigroup)

  IdentifiableInstance
  (unwrap [this] elem)

  SectionElement
  (tag [this] 0)
  (member [this] elem)

  AbstractMorphism
  (source-object [this] 0)
  (target-object [this] 0))

(derive SemigroupElement :locus.set.logic.structure.protocols/element)

(defmethod wrap :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup elem]

  (->SemigroupElement semigroup elem))

; Composition of semigroup elements
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

; Ontology of semigroup elements
(defn semigroup-element?
  [elem]

  (= (type elem) SemigroupElement))