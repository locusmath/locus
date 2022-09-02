(ns locus.elementary.action.global.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.action.effects.transformation :refer :all]
            [locus.elementary.action.global.object :refer :all])
  (:import (locus.elementary.action.global.object MSet)))

; Let M be a monoid. Then Sets^M is a topos of monoid actions over the monoid M.
; This topos has both a set of objects and a set of morphisms. This file provides
; supports for morphisms in these fundamental topoi.

; Morphisms in the topos of monoid actions
(deftype EquivariantMap [source-mset target-mset func]
  AbstractMorphism
  (source-object [this] source-mset)
  (target-object [this] target-mset)

  ConcreteMorphism
  (inputs [this] (underlying-set source-mset))
  (outputs [this] (underlying-set target-mset))

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive EquivariantMap :locus.elementary.function.core.protocols/equivariant-map)

; Composition and identities in the topos of monoid actions
(defmethod compose* EquivariantMap
  [f g]

  (EquivariantMap.
    (source-object g)
    (target-object f)
    (fn [a]
      (f (g a)))))

(defn identity-equivariant-map
  [ms]

  (EquivariantMap.
    ms
    ms
    identity))

(defmethod identity-morphism MSet
  [ms] (identity-equivariant-map ms))

; Subobject classifier in the topos of monoid actions
(comment
 (defn truth-mset
   [monoid]

   (MSet.
     monoid
     (mset-subalgebras (left-self-action monoid))
     (fn [action ideal]
       (set
         (filter
           (fn [n]
             (contains? ideal (monoid (list n action))))
           (underlying-set monoid))))))

 (defn submset-character
   [ms ideal]

   (let [monoid (.monoid ms)]
     (EquivariantMap.
       ms
       (truth-mset monoid)
       (fn [y]
         (set
           (filter
             (fn [m]
               (contains? ideal (monoid (list m y))))
             (underlying-set monoid))))))))

; Ontology of morphisms in the topos of monoid actions
(defn equivariant-map?
  [func]

  (= (type func) EquivariantMap))