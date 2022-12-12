(ns locus.order.lattice.combinat.impl
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.numeric.nms :refer :all]
            [locus.set.logic.numeric.sig :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.incidence.signatures.nf :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.lattice.core.object Lattice)))

; Intervals lattice
(defn join-intervals*
  [pair1 pair2]

  (cond
    (empty? pair1) pair2
    (empty? pair2) pair1
    :else (let [[a b] pair1
                [c d] pair2]
            [(min a c)
             (max b d)])))

(defn meet-intervals*
  [pair1 pair2]

  (cond
    (empty? pair1) []
    (empty? pair2) []
    :else (let [[a b] pair1
                [c d] pair2]
            (let [new-start (max a c)
                  new-end (min b d)]
              (if (<= new-start new-end)
                [new-start new-end]
                [])))))

(defn interval-lattice
  [n]

  (Lattice.
    (all-intervals n)
    (monoidalize join-intervals*)
    (monoidalize meet-intervals*)))

; Noncrossing partition lattice
(defn noncrossing-partition-lattice
  [n]

  (Lattice.
    (set
      (filter
        noncrossing-range-partition?
        (set-partitions (set (range n)))))
    join-noncrossing-partitions
    meet-set-partitions))

; Get a lattice from a Moore family and its closure operation
(defn moore-lattice
  [family]

  (Lattice.
    (dimembers family)
    (fn [& args]
      (cl family (apply union args)))
    intersection))

; Youngs lattice of additive partitions
(def youngs-lattice
  (Lattice.
    additive-partition?
    young-join
    young-meet))


