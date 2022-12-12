(ns locus.hyper.mapping.transformation
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.function.image.image-function :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.effects.global.transformation :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.hyper.mapping.function :refer :all]))

; A hypertransformation is an endomorphism in the concrete category Rel of sets and hyperfunctions.
(deftype Hypertransformation [coll func]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Hypertransformation :locus.hyper.mapping.function/hypertransformation)

; Identity hypertransformations
(defn identity-hypertransformation
  [coll]

  (Hypertransformation.
    coll
    (fn [i]
      #{i})))

(defmethod compose* Hypertransformation
  [a b]

  (Hypertransformation.
    (source-object b)
    (fn [x]
     (apply union (map a (b x))))))

; Conversion routines for hypertransformations
(defmulti to-hypertransformation type)

(defmethod to-hypertransformation Hypertransformation
  [transformation] transformation)

(defmethod to-hypertransformation :locus.set.logic.structure.protocols/transformation
  [func]

  (->Hypertransformation
    (source-object func)
    (fn [i]
      #{(func i)})))