(ns locus.elementary.relation.general.mr
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.general.rel :refer :all]))

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