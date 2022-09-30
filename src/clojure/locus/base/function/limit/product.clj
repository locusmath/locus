(ns locus.base.function.limit.product
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all])
  (:import (locus.base.partition.core.object ProductPartition CoproductPartition)))

; Product function
; A special class representing products in the topos of functions.
(deftype ProductFunction [funcs]
  ConcreteMorphism
  (inputs [this]
    (->CartesianProduct (map inputs funcs)))
  (outputs [this]
    (->CartesianProduct (map outputs funcs)))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this obj]
    (map-indexed
      (fn [i v]
        ((nth funcs i) v))
      obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ProductFunction :locus.base.logic.structure.protocols/set-function)

(defmethod image [ProductFunction ProductPartition]
  [^ProductFunction func, ^ProductPartition partition]

  (let [funcs (.-funcs func)
        partitions (.-partitions partition)]
    (ProductPartition.
      (map-indexed
       (fn [i v]
         (image (nth funcs i) v))
       partitions))))

; Coproduct function
; A special class representing coproducts in the topos of functions
(deftype CoproductFunction [funcs]
  ConcreteMorphism
  (inputs [this]
    (->CartesianCoproduct (map inputs funcs)))
  (outputs [this]
    (->CartesianCoproduct (map outputs funcs)))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this [i v]]
    (list i ((nth funcs i) v)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive CoproductFunction :locus.base.logic.structure.protocols/set-function)

(defmethod image [CoproductFunction CoproductPartition]
  [^CoproductFunction func, ^CoproductPartition partition]


  (let [funcs (.-funcs func)
        partitions (.-partitions partition)]
    (CoproductPartition.
      (map-indexed
        (fn [i v]
          (image (nth funcs i) v))
        partitions))))
