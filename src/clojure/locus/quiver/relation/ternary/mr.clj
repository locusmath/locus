(ns locus.quiver.relation.ternary.mr
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.vertexset :refer :all]
            [locus.quiver.relation.ternary.op :refer :all]))

; The class provided in this file, MagmaRelation, supports the description of
; magmas and related binary operations as sets of ordered triples, well saving
; you from having to actually list out all the ordered triples yourself. It
; implements the seqable interface, so that you can get all ordered triples only
; when you need them.

; Magma relations
(deftype MagmaRelation [vertices func]
  clojure.lang.Seqable
  (seq [this]
    (map
      (fn [pair]
        (let [[a b] pair]
          (list a b (func pair))))
      (cartesian-power vertices 2)))

  clojure.lang.Counted
  (count [this]
    (let [vertex-count (count vertices)]
      (* vertex-count vertex-count)))

  clojure.lang.IFn
  (invoke [this [a b c]]
    (= (func (list a b)) c))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive MagmaRelation :locus.base.logic.core.set/universal)

; The vertices of a seqable magma are defined by an instance field
(defmethod vertices MagmaRelation
  [^MagmaRelation rel]

  (.vertices rel))

; Composition relations of semigroups
(defn composition-relation
  [func]

  (MagmaRelation. (underlying-set func) func))