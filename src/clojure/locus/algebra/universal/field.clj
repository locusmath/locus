(ns locus.algebra.universal.field
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.function.core.util :refer :all]))

; Topos theoretic type system:
; The topos theoretic type system extends the JVM type system to support
; a variety of structured sets with functorial field accessors, extending
; the default field accessors on the JVM.

; Topos composite structures
(defprotocol ToposCompositeStructure
  (topos-fields [this])
  (topos-field-type [this name]))

; Topos composite elements allowing for functorial field access
(defprotocol ToposCompositeElement
  (tload [this name]))

; Topos field types
(defprotocol ToposField
  (transform [this name arg]))

(deftype SimpleToposFieldType [id]
  ToposField
  (transform [this name morphism]
    (underlying-function morphism)))

(deftype TotalOperatorFieldType [id arity]
  ToposField
  (transform [this name morphism]
    (let [func (underlying-function morphism)]
      (->Diamond
        (tload (source-object morphism) name)
        (tload (target-object morphism) name)
        (apply function-product (repeat arity func))
        func))))

(deftype PartialOperatorFieldType [id arity]
  ToposField
  (transform [this name morphism]
    (let [func (underlying-function morphism)
          src (tload (source-object morphism) name)
          target (tload (target-object morphism) name)]
      (->Diamond
        src
        target
        (->SetFunction
          (inputs src)
          (inputs target)
          (fn [coll]
            (map func coll)))
        func))))

(deftype RelationalFieldType [id arity]
  ToposField
  (transform [this name morphism]
    (let [func (underlying-function morphism)]
      (->SetFunction
        (tload (source-object morphism) name)
        (tload (target-object morphism) name)
        (fn [coll]
          (map func coll))))))

(deftype EdgeSetFieldType [id]
  ToposField
  (transform [this name morphism]
    (->SetFunction
      (tload (source-object morphism) name)
      (tload (target-object morphism) name)
      (fn [coll]
        (set (map morphism coll))))))




