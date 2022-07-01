(ns locus.algebra.universal.structure
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.algebra.universal.field :refer :all])
  (:import (locus.algebra.universal.field SimpleToposFieldType TotalOperatorFieldType PartialOperatorFieldType RelationalFieldType)))

; General homomorphism functions applicable to numerous structures
; This is the morphism part of the topos theoretic type system
(deftype HomomorphismFunction [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  ToposCompositeElement
  (tload [this name]
    (let [type (topos-field-type source name)]
      (transform type name this)))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(defmethod compose* HomomorphismFunction
  [a b]

  (HomomorphismFunction.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

; The category of nary relations on a set
(deftype RelationalSet [vertices edges arity]
  ConcreteObject
  (underlying-set [this] vertices)

  ToposCompositeStructure
  (topos-fields [this] #{"S" "edges"})
  (topos-field-type [this name]
    (case name
      "S" (SimpleToposFieldType. "sets")
      "edges" (RelationalFieldType. "sets" 2)))

  ToposCompositeElement
  (tload [this name]
    (case name
      "S" vertices
      "edges" edges)))

;(def exdg
;  (RelationalSet.
;    #{0 1 2}
;    '#{(0 1) (1 2) (0 2)}
;    2))
;
;(def otherdg
;  (RelationalSet.
;    '#{3 4}
;    '#{(3 3) (3 4) (4 4)}
;    2))
;
;(def mdg
;  (HomomorphismFunction.
;    exdg
;    otherdg
;    {0 3, 1 3, 2 4}))

