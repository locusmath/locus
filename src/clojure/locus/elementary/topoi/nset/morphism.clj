(ns locus.elementary.topoi.nset.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.topoi.nset.object :refer :all])
  (:import (locus.elementary.diset.core.object Diset)
           (locus.elementary.topoi.nset.object NSet)
           (locus.elementary.difunction.core.object Difunction)))

; Let Sets^n be a topos of copresheaves over a discrete category with n elements. Then morphisms
; in one of these fundamental topoi of copresheaves can be described by the data of an array
; of n functions. Thus we define the class NFunction to handle this type of generalized structure.
; The to-copresheaf method converts these back into copresheaves over their underlying
; generalized discrete categories.

(deftype NFunction [funcs]
  AbstractMorphism
  (source-object [this]
    (NSet. (map inputs funcs)))
  (target-object [this]
    (NSet. (map outputs funcs))))

(defn nth-function
  [^NFunction func, i]

  (nth (.funcs func) i))

; Conversion routines for morphisms in presheaf topoi over discrete categorise
(defmulti to-nfunction type)

(defmethod to-nfunction NFunction
  [func] func)

(defmethod to-nfunction Difunction
  [func]

  (NFunction. [(first-function func) (second-function func)]))

; Composition and identities in toposes of copresheaves over discrete categories
(defmethod identity-morphism NSet
  [^NSet coll]

  (NFunction.
    (map
      identity-function
      (.colls coll))))

(defmethod compose* NFunction
  [a b]

  (let [n (count (.funcs a))]
    (NFunction.
      (map
        (fn [i]
          (compose (nth-function a i) (nth-function b i)))
        (range n)))))

; Ontology of morphisms of copresheaves over discrete categories
(defn nfunction?
  [func]

  (= (type func) NFunction))