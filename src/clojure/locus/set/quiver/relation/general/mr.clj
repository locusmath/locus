(ns locus.set.quiver.relation.general.mr
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.general.rel :refer :all]))

; Ontology of multirelations
(defn multirelation?
  [coll]

  (and
   (multiset? coll)
   (every? seq? coll)))

(def size-two-multirelation?
  (intersection
    size-two-multiset?
    multirelation?))

(def size-three-multirelation?
  (intersection
    size-two-multiset?
    multirelation?))

(def size-four-multirelation?
  (intersection
    size-two-multiset?
    multirelation?))