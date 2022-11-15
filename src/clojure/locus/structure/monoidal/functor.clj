(ns locus.structure.monoidal.functor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.concrete.concrete-category :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.category.concrete.categories :refer :all])
  (:import (locus.elementary.semigroup.monoid.object Monoid)
           (locus.elementary.semigroup.monoid.morphism MonoidMorphism)))

; A presheaf of monoids is a functor F: C -> Mon. It is a generalisation of a presheaf of abelian
; groups. Additionally, when we later consider presheaves of commutative unital rings it is useful
; to consider the underlying additive presheaves of abelian groups and multiplicative
; presheaves of monoids both of which are part of the presheaf of monoids theory. We also note
; that presheaves of monoids are always special types of category-valued functors.

(deftype MonoidalFunctor [index object-function morphism-function]
  AbstractMorphism
  (source-object [this] index)
  (target-object [this] set-monoids)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive MonoidalFunctor :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; Monoidal functors are structure presheaves, so they have underlying objects and morphisms
(defmethod get-object MonoidalFunctor
  [functor x]

  ((second-function functor) x))

(defmethod get-function MonoidalFunctor
  [functor x]

  ((first-function functor) x))

; Monoidal functors are structure presheaves, so they have underlying copresheaves in a topos
(defmethod get-set MonoidalFunctor
  [functor x]

  (underlying-set (get-object functor x)))

(defmethod get-function MonoidalFunctor
  [functor x]

  (underlying-function (get-morphism functor x)))

; As structure presheaves, monoidal functors are always defined relative to some index category
(defmethod index MonoidalFunctor
  [^MonoidalFunctor functor]

  (.-index functor))

; Every single monoidal functor can be converted from a structure presheaf back into an functor
(defmethod to-functor MonoidalFunctor
  [^MonoidalFunctor functor]

  (->Functor
    (source-object functor)
    (target-object functor)
    (partial get-object functor)
    (partial get-morphism functor)))

; As structure copresheaves, monoidal functors have underlying copresheaves
(defmethod to-copresheaf MonoidalFunctor
  [^MonoidalFunctor functor]

  (->Copresheaf
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Generalized conversion routines for presheaves of monoids
(defmulti to-monoidal-functor type)

(defmethod to-monoidal-functor MonoidalFunctor
  [functor] functor)

(defmethod to-monoidal-functor Monoid
  [monoid]

  (->MonoidalFunctor
    (thin-category (weak-order [#{0}]))
    (constantly monoid)
    (constantly (identity-morphism monoid))))

(defmethod to-monoidal-functor MonoidMorphism
  [morphism]

  (->MonoidalFunctor
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object morphism)
        1 (target-object morphism)))
    (fn [[a b]]
      (case [[a b]]
        [0 0] (identity-morphism (source-object morphism))
        [0 1] morphism
        [1 1] (identity-morphism (target-object morphism))))))

; Create special types of monoid functors
(defn dimonoid
  [a b]

  (->MonoidalFunctor
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 a
        1 b))
    (fn [[x y]]
      (case [x y]
        [0 0] (identity-morphism a)
        [1 1] (identity-morphism b)))))

(defn monoid-isomorphism-functor
  [forwards backwards]

  (->MonoidalFunctor
    (thin-category (total-preorder [#{0 1}]))
    (fn [obj]
      (case obj
        0 (source-object forwards)
        1 (target-object forwards)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-morphism (source-object forwards))
        [1 1] (identity-morphism (target-object forwards))
        [0 1] forwards
        [1 0] backwards))))

; Ontology of monoidal functors
(defn monoidal-functor?
  [functor]

  (= (type functor) MonoidalFunctor))

(defn chain-of-monoids?
  [functor]

  (and
    (monoidal-functor? functor)
    (total-order-category? (index functor))))

(defn monoid-object-functor?
  [functor]

  (and
    (monoidal-functor? functor)
    (let [cat (index functor)]
      (= (count (objects cat)) (count (morphisms cat)) 1))))

(defn monoid-morphism-functor?
  [functor]

  (and
    (monoidal-functor? functor)
    (let [cat (index functor)]
      (and
        (total-order-category? cat)
        (= (count (objects cat)) 2)))))

(defn monoid-isomorphism-functor?
  [functor]

  (and
    (monoidal-functor? functor)
    (let [cat (index functor)]
      (and
        (complete-thin-groupoid? cat)
        (= (count (objects cat)) 2)))))

(defn monoid-triangle?
  [functor]

  (and
    (monoidal-functor? functor)
    (let [cat (index functor)]
      (and
        (total-order-category? cat)
        (= (count (objects cat)) 3)))))

(defn dimonoid?
  [functor]

  (and
    (monoidal-functor? functor)
    (let [cat (index functor)]
      (and
        (discrete-category? cat)
        (= (count (objects cat)) 2)))))

(defn nmonoid?
  [functor]

  (and
    (monoidal-functor? functor)
    (discrete-category? (index functor))))

(defn monoid-diamond?
  [functor]

  (and
    (monoidal-functor? functor)
    (diamond-category? (index functor))))