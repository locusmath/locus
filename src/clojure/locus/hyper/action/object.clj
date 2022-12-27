(ns locus.hyper.action.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.hyper.mapping.function :refer :all]
            [locus.hyper.mapping.transformation :refer :all]
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
            [locus.set.action.global.object :refer :all]
            [locus.algebra.category.concrete.categories :refer :all])
  (:import (locus.set.action.global.object MSet)))

; A hyper MSet is a functor from a monoid to the category of sets and multivalued functions.
(deftype HyperMSet [monoid coll func]
  AbstractMorphism
  (source-object [this] monoid)
  (target-object [this] rel)

  StructuredDifunction
  (first-function [this] (constantly coll))
  (second-function [this] func))

(derive HyperMSet :locus.set.copresheaf.structure.core.protocols/structure-copresheaf)

; Hyper monoid actions as structure copresheaves
(defmethod index HyperMSet
  [^HyperMSet mset]

  (.-monoid mset))

(defmethod get-object HyperMSet
  [^HyperMSet mset, x]

  (object-apply mset x))

(defmethod get-morphism HyperMSet
  [^HyperMSet mset, action]

  (morphism-apply mset action))

(defmethod get-set HyperMSet
  [^HyperMSet mset, x]

  (get-object mset x))

(defmethod get-function HyperMSet
  [^HyperMSet mset, action]

  (to-function (get-morphism mset action)))

; Convert objects into hyper monoid actions
(defmulti to-hypermset type)

(defmethod to-hypermset HyperMSet
  [^HyperMSet mset] mset)

(defmethod to-hypermset MSet
  [^MSet mset]

  (->HyperMSet
    (index mset)
    (underlying-set mset)
    (fn [i]
      (to-hyperfunction (action-function mset i)))))

; Images and inverse images of hyper monoid actions
(defn hypertransformations-list
  [^HyperMSet mset]

  (map
    (fn [i]
      (get-morphism mset i))
    (morphisms (index mset))))

(defn hypermset-set-image
  [hypermset coll]

  (let [hyperfunctions (hypertransformations-list hypermset)]
    (apply
      union
      (map
        (fn [hyperfunction]
          (hyperfunction-set-image hyperfunction coll))
        hyperfunctions))))

(defn hypermset-set-inverse-image
  [hypermset coll]

  (set
    (filter
      (fn [i]
        (superset? (list (hypermset-set-image hypermset #{i}) coll)))
      (underlying-set hypermset))))

(defmethod image
  [HyperMSet :locus.set.logic.core.set/universal]
  [action coll]

  (hypermset-set-image action coll))

(defmethod inverse-image
  [HyperMSet :locus.set.logic.core.set/universal]
  [action coll]

  (hypermset-set-inverse-image action coll))

; Ontology of hyper monoid actions
(defn hypermset?
  [action]

  (= (type action) HyperMSet))