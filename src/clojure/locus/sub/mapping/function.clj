(ns locus.sub.mapping.function
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.inclusion.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; A subfunction of a function f: A -> B is a homomorphism of unary relations, or subsets in A
; and B. So in other words, for subsets like S of A and T of B then this means that the f(S)
; image is contained in B. These are then morphisms in a category of unary relations, and
; subalgebras can be composed accordingly.
(deftype SetSubfunction [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this obj]
    (func obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive SetSubfunction :locus.base.logic.structure.protocols/structured-function)

; Included inputs and outputs
(defn included-inputs
  [func]

  (included-elements (source-object func)))

(defn included-outputs
  [func]

  (included-elements (target-object func)))

(defn included-transition
  [func]

  (list (included-inputs func) (included-outputs func)))

; A constuctor for set subfunctions
(defn set-subfunction
  [func a b]

  (->SetSubfunction
    (set-subalgebra a (inputs func))
    (set-subalgebra b (outputs func))
    func))

; Conversion routines
(defmulti to-set-subfunction type)

(defmethod to-set-subfunction SetSubfunction
  [func] func)

(defmethod to-set-subfunction SetFunction
  [func]

  (->SetSubfunction
    (full-set-subalgebra (inputs func))
    (full-set-subalgebra (outputs func))
    func))

; Subalgebras have all products and coproducts
(defmethod coproduct SetSubfunction
  [& functions]

  (->SetSubfunction
    (apply coproduct (map source-object functions))
    (apply coproduct (map target-object functions))
    (fn [[i v]]
      (list i ((nth functions i) v)))))

(defmethod product SetSubfunction
  [& functions]

  (->SetSubfunction
    (apply product (map source-object functions))
    (apply product (map target-object functions))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth functions i) v))
        coll))))

; Ontology of set subfunctions
(defn set-subfunction?
  [obj]

  (= (type obj) SetSubfunction))
