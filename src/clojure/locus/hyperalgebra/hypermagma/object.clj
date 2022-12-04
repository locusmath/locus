(ns locus.hyperalgebra.hypermagma.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.invertible.function.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.hyper.mapping.function :refer :all]
            [locus.nonassociative.magma.object :refer :all])
  (:import (locus.nonassociative.magma.object Magma)))

; Hyperstructures are algebraic structures equipped with multi-valued operations called
; hyperfunctions. In other words, they are algebraic structures internal to the concrete category
; Rel of sets and multivalued functions. A good starting point are hypermagmas which are
; magmas internal to the category Rel of sets and hyperfunctions. Hyperstructures have applications
; to a wide variety of mathematical theories including partition theory.

(deftype Hypermagma [coll func]
  AbstractMorphism
  (source-object [this] (complete-relation coll))
  (target-object [this] coll)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Hypermagma :locus.base.logic.structure.protocols/structured-set)

; Conversion mechanisms for internalising hypermagmas into the concrete category Rel
(defmethod to-hyperfunction Hypermagma
  [^Hypermagma magma]

  (->Hyperfunction
    (complete-relation (.-coll magma))
    (.-coll magma)
    (.-func magma)))

(defmethod to-function Hypermagma
  [^Hypermagma magma]

  (to-function (to-hyperfunction magma)))

; Conversion routines for hypermagmas
(defmulti to-hypermagma type)

(defmethod to-hypermagma Hypermagma
  [magma] magma)

(defmethod to-hypermagma Magma
  [magma]

  (->Hypermagma
    (underlying-set magma)
    (fn [[a b]]
      #{(magma (list a b))})))

; Ontology of hyperstructures
(defn hypermagma?
  [obj]

  (= (type obj) Hypermagma))