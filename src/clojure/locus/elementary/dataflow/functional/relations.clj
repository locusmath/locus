(ns locus.elementary.dataflow.functional.relations
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.dataflow.functional.decomposition :refer :all]))

; A flow model is an abstract of a congruences system of a function, where
; a congruence of a function is defined by the topos of functions. It is typically
; accompanied by a function, for which the flow model applies.
(deftype FlowModel [in out rel]
  StructuredDiset
  (first-set [this] (underlying-set in))
  (second-set [this] (underlying-set out)))

; The main purpose of the flow model is to convert relations into congruences
; It is responsible for the modeling of congruences in the topos of functions in terms
; of morphisms in the allegory of sets and relations.
(defn flow-congruence
  [model a b]

  (list (get-equivalence-relation (.in model) a)
        (get-equivalence-relation (.out model) b)))