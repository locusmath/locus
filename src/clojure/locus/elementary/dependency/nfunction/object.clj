(ns locus.elementary.dependency.nfunction.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.dependency.nset.object :refer :all])
  (:import (locus.elementary.diset.core.object Diset)
           (locus.elementary.difunction.core.object Difunction)
           (locus.base.function.core.object SetFunction)
           (locus.elementary.dependency.nset.object NSet)))

; Let Sets^(T_2+T_2...) be the topos of copresheaves over the disjoint union of ordered pair
; categories. Then the objects of this presheaf topos are collections of set functions
; in the topos Sets^(T_2) which is also the arrow category of the topos of Sets and functions.
; In other words, this is a product topos of Sets^(T_2) topoi. The objects of this topos
; can also be explained as morphisms in the topos Sets^n of copresheaves over a
; discrete category with n elements.

(deftype NFunction [funcs]
  AbstractMorphism
  (source-object [this]
    (NSet. (map inputs funcs)))
  (target-object [this]
    (NSet. (map outputs funcs))))

(defn nth-function
  [^NFunction func, i]

  (nth (.funcs func) i))

(defn nfunction-type
  [^NFunction func]

  (count (.funcs func)))

; Conversion routines for morphisms in presheaf topoi over discrete categorise
(defmulti to-nfunction type)

(defmethod to-nfunction NFunction
  [func] func)

(defmethod to-nfunction Difunction
  [func]

  (NFunction. [(first-function func) (second-function func)]))

(defmethod to-nfunction SetFunction
  [func]

  (NFunction. [func]))

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

; Products and coproducts in copresheaf topoi over disjoint unions of ordered pair categories
(defmethod product NFunction
  [& args]

  (NFunction.
    (let [n (nfunction-type (first args))]
      (map
        (fn [i]
          (apply product (map #(nth-function % i) args)))
        (range n)))))

(defmethod coproduct NFunction
  [& args]

  (NFunction.
    (let [n (nfunction-type (first args))]
      (map
        (fn [i]
          (apply coproduct (map #(nth-function % i) args)))
        (range n)))))

; Ontology of morphisms of copresheaves over discrete categories
(defn nfunction?
  [func]

  (= (type func) NFunction))

