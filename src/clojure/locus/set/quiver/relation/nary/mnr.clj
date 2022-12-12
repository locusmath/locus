(ns locus.set.quiver.relation.nary.mnr
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.set.quiver.relation.binary.mbr :refer :all]
            [locus.set.quiver.relation.ternary.op :refer :all]
            [locus.set.quiver.relation.ternary.tr :refer :all]
            [locus.set.quiver.relation.nary.product :refer :all]
            [locus.set.quiver.relation.unary.ur :refer :all]
            [locus.set.quiver.relation.quaternary.qr :refer :all]))

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




