(ns locus.partial.action.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.partial.mapping.transformation :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.core.morphism :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.set.action.core.protocols :refer :all]
            [locus.set.action.global.object :refer :all])
  (:import (locus.set.action.global.object MSet)))

; A partial MSet is a partial copresheaf on a monoid, or a functor F: M -> Sets_{Part} into the
; category of sets and partial functions. Every monoid of partial transformations, including
; the full partial transformation monoid on a set naturally induces a partial mset. Many
; constructions from ordinary MSet theory generalize to their partial counterparts.

(deftype PartialMSet [monoid coll action]
  ConcreteObject
  (underlying-set [this] coll)

  EffectSystem
  (actions [this]
    (morphisms monoid))
  (action-domain [this elem]
    (relation-domain (underlying-relation (action elem))))
  (apply-action [this elem arg]
    ((action elem) arg)))

(derive PartialMSet :locus.set.logic.structure.protocols/structured-set)

; Index categories for partial monoid actions
(defmethod index PartialMSet
  [^PartialMSet mset]

  (.-monoid mset))

; Partial monoid actions as structure copresheaves
(defmethod get-object PartialMSet
  [^PartialMSet mset, x]

  (underlying-set mset))

(defmethod get-morphism PartialMSet
  [^PartialMSet mset, i]

  ((.-action mset) i))

(defmethod get-set PartialMSet
  [action i]

  (multiselection (get-object action i) #{0 1}))

(defmethod get-function PartialMSet
  [action i]

  (to-function (get-morphism action i)))

; Generalized conversion routines for partial monoid actions
(defmulti to-partial-mset type)

(defmethod to-partial-mset PartialMSet
  [partial-mset] partial-mset)

(defmethod to-partial-mset MSet
  [mset]

  (let [coll (underlying-set mset)]
    (->MSet
     (index mset)
     coll
     (fn [a]
       (->PartialTransformation
         coll
         coll
         (fn [x]
           (apply-action mset a x)))))))

; Action preorders for partial msets
(defmethod action-preorder PartialMSet
  [^PartialMSet mset]

  (apply
    union
    (map
      (fn [i]
        (let [partial-transformation (get-object mset i)]
          (underlying-relation partial-transformation)))
      (actions mset))))

; Get a collection of all partial transformations from a partial mset
(defn partial-transformations-list
  [^PartialMSet mset]

  (map
    (fn [i]
      (get-morphism mset i))
    (actions mset)))

; Ontology of partial msets
(defn partial-mset?
  [obj]

  (= (type obj) PartialMSet))
