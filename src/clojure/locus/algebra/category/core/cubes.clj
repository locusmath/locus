(ns locus.algebra.category.core.cubes
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

; Support for cubical structures
(defn array-of-bits-to-integer
  [bits]

  (int
    (apply
      +
      (map-indexed
       (fn [i v]
         (if (zero? v)
           0
           (Math/pow 2 i)))
       (reverse bits)))))

(defn access-array-by-bits
  [coll bits]

  (nth coll (array-of-bits-to-integer bits)))

(defn get-face-by-region
  [coll regions]

  (map
    (fn [bits]
      (access-array-by-bits coll bits))
    regions))

(defn get-bits
  [n]

  (letfn [(bits [n]
            (if (< n 2)
              [n]
              (conj (bits (quot n 2)) (rem n 2))))]
    (vec (reverse (bits n)))))

(defn pad-vector
  [nums new-size]

  (let [len (count nums)]
    (vec
     (map
       (fn [i]
         (if (< i len)
           (nth nums i)
           0))
       (range new-size)))))

(defn get-all-regions
  [n]

  (map
    (fn [i]
      (pad-vector (get-bits i) n))
    (range (int (Math/pow 2 n)))))

; Face coordinates
(def cube-bottom
  [[0 0 0] [0 0 1] [0 1 0] [0 1 1]])

(def cube-top
  [[1 0 0] [1 0 1] [1 1 0] [1 1 1]])

(def cube-vertical-source-face
  [[0 0 0] [0 0 1] [1 0 0] [1 0 1]])

(def cube-vertical-target-face
  [[0 1 0] [0 1 1] [1 1 0] [1 1 1]])

(def cube-horizontal-source-face
  [[0 0 0] [0 1 0] [1 0 0] [1 1 0]])

(def cube-horizontal-target-face
  [[0 0 1] [0 1 1] [1 0 1] [1 1 1]])

