(ns locus.quiver.relation.nary.mnr
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.vertexset :refer :all]
            [locus.quiver.relation.binary.mbr :refer :all]
            [locus.quiver.relation.ternary.op :refer :all]
            [locus.quiver.relation.ternary.tr :refer :all]
            [locus.quiver.relation.nary.product :refer :all]
            [locus.quiver.relation.unary.ur :refer :all]
            [locus.quiver.relation.quaternary.qr :refer :all]))

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




