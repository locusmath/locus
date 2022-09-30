(ns locus.elementary.difunction.dibijection.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.invertible.function.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.diset.core.object Diset)))

; A dibijection is an object of the elementary copresheaf topos Sets^{K_2 + K_2}
; A dibijection is like an invertible difunction, except it already comes equipped
; with its own inverse.
(deftype Dibijection [f g]
  StructuredDifunction
  (first-function [this] (underlying-function f))
  (second-function [this] (underlying-function g))

  StructuredDibijection
  (first-bijection [this] f)
  (second-bijection [this] g)

  Invertible
  (inv [this]
    (Dibijection.
      (inv f)
      (inv g)))

  AbstractMorphism
  (source-object [this]
    (Diset. (inputs f) (inputs g)))
  (target-object [this]
    (Diset. (outputs f) (outputs g)))

  ConcreteMorphism
  (inputs [this]
    (underlying-set (source-object this)))
  (outputs [this]
    (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i 0) (list 0 (f v))
      (= i 1) (list 1 (g v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Dibijection :locus.elementary.copresheaf.core.protocols/structured-difunction)

; Convert a dibijection into a pair of invertible functions
(defmethod to-difunction Dibijection
  [^Dibijection func]

  (->Difunction
    (to-invertible-function (first-bijection func))
    (to-invertible-function (second-bijection func))))

; Composition and identities in the groupoid of set pairs
(defn identity-dibijection
  [coll]

  (Dibijection.
    (identity-bijection coll)
    (identity-bijection coll)))

(defmethod compose* Dibijection
  [a b]

  (Dibijection.
    (compose (first-bijection a) (first-bijection b))
    (compose (second-bijection a) (second-bijection b))))

; Invert component bijections
(defn invert-first-bijection
  [dibijection]

  (Dibijection.
    (inv (first-bijection dibijection))
    (second-bijection dibijection)))

(defn invert-second-bijection
  [dibijection]

  (Dibijection.
    (first-bijection dibijection)
    (inv (second-bijection dibijection))))

; Constructors for dibijections
(defn dibijection
  ([obj]
   (if (or (vector? obj) (seq? obj))
     (Dibijection. (first obj) (second obj))
     (Dibijection. (first-bijection obj) (second-bijection obj))))
  ([a b]
   (Dibijection. a b)))

(defn equal-dibijection
  [func]

  (Dibijection. func func))

(defmulti to-dibijection type)

(defmethod to-dibijection Dibijection
  [func] func)

(defmethod to-dibijection :locus.elementary.copresheaf.core.protocols/difunction
  [func]

  (if (not (invertible-difunction? func))
    (throw (new IllegalArgumentException))
    (->Dibijection
      (to-bijection (first-function func))
      (to-bijection (second-function func)))))

; Products and coproducts in the topos of dibijections
(defn dibijection-product
  [& dibijections]

  (Dibijection.
    (apply bijection-product (map first-bijection dibijections))
    (apply bijection-product (map second-bijection dibijections))))

(defn dibijection-coproduct
  [& dibijections]

  (Dibijection.
    (apply bijection-coproduct (map first-bijection dibijections))
    (apply bijection-coproduct (map second-bijection dibijections))))

(defmethod product Dibijection
  [& dibijections]

  (apply dibijection-product dibijections))

(defmethod coproduct Dibijection
  [& dibijections]

  (apply dibijection-coproduct dibijections))

; Subalgebras in the topos of dibijections
(defn subdibijection?
  [dibijection [a c] [b d]]

  (and
    (bijection-subobject? (first-bijection dibijection) a b)
    (bijection-subobject? (second-bijection dibijection) c d)))

(defn subdibijection
  [dibijection [a c] [b d]]

  (Dibijection.
    (subbijection (first-bijection dibijection) a b)
    (subbijection (second-bijection dibijection) c d)))

; Quotients in the topos of dibijections
(defn dibijection-congruence?
  [dibijection [a c] [b d]]

  (and
    (bijection-congruence? (first-bijection dibijection) a b)
    (bijection-congruence? (second-bijection dibijection) c d)))

(defn quotient-dibijection
  [dibijection [a c] [b d]]

  (Dibijection.
    (quotient-bijection (first-bijection dibijection) a b)
    (quotient-bijection (second-bijection dibijection) c d)))

; Ontology of dibijections
(defn dibijection?
  [func]

  (= (type func) Dibijection))

(defn identity-dibijection?
  [func]

  (and
    (dibijection? func)
    (identity-bijection? (first-bijection func))
    (identity-bijection? (second-bijection func))))
