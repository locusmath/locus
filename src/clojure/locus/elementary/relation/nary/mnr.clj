(ns locus.elementary.relation.nary.mnr
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.ternary.op :refer :all]
            [locus.elementary.relation.ternary.tr :refer :all]
            [locus.elementary.relation.nary.product :refer :all]
            [locus.elementary.relation.unary.ur :refer :all]
            [locus.elementary.relation.quaternary.qr :refer :all]))

; Other classes of multirelations
(defn nary-multirelation?
  [rel]

  (and
    (multiset? rel)
    (every? seq? rel)
    (or
      (empty? rel)
      (apply = (map count rel)))))

(def equal-nary-multirelation?
  (intersection
    equal-multiset?
    nary-multirelation?))



































