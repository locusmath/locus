(ns locus.elementary.relation.general.mr
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
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