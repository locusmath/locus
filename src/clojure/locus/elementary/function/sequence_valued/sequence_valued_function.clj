(ns locus.elementary.function.sequence-valued.sequence-valued-function
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.util :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

; A sequence valued function is a function f: S -> X where the set X consists of words of the free semigroup
; on a set, or in other words X consists of elements of the sequence data type. Special cases include
; nary sequence valued functions which are maps f : S -> T^n which map a set to the cartesian product of
; sets. Sequence valued functions are dual to operation which are functions f : X -> S for which the input
; set is a family of sequences.

; Concatenate functions together
(defn concat-functions
  "These functions need to have a common input"
  [& functions]

  (when (not (empty? functions))
    (SetFunction.
      (inputs (first functions))
      (apply cartesian-product (map outputs functions))
      (fn [x]
        (map (fn [f] (f x)) functions)))))

(defn repeat-function-outputs
  [func n]

  (SetFunction.
    (inputs func)
    (cartesian-power (outputs func) n)
    (fn [i]
      (repeat n (func i)))))

; Ontology of sequence valued functions
(defn sequence-valued-function?
  [func]

  (and
    (set-function? func)
    (every?
      (fn [i]
        (seq? (func i)))
      (inputs func))))

(defn nary-sequence-valued-function?
  [func]

  (and
    (sequence-valued-function? func)
    (equal-seq?
      (map
        (fn [i]
          (count (func i)))
        (inputs func)))))

(defn singular-sequence-valued-function?
  [func]

  (and
    (set-function? func)
    (every?
      (fn [i]
        (singular-seq? (func i)))
      (inputs func))))

(defn ordered-pair-valued-function?
  [func]

  (and
    (set-function? func)
    (every?
      (fn [i]
        (size-two-seq? (func i)))
      (inputs func))))

(defn ordered-triple-valued-function?
  [func]

  (and
    (set-function? func)
    (every?
      (fn [i]
        (size-three-seq? (func i)))
      (inputs func))))

(defn ordered-quadruple-valued-function?
  [func]

  (and
    (set-function? func)
    (every?
      (fn [i]
        (size-four-seq? (func i)))
      (inputs func))))