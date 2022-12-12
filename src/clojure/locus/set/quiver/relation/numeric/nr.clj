(ns locus.set.quiver.relation.numeric.nr
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.numeric.nms :refer :all]
            [locus.set.logic.numeric.sig :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.numeric-sequence.np :refer :all]
            [locus.set.logic.numeric-sequence.onms :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]))

; Numeric relations are simply relations with numeric vertices
(defn numeric-relation?
  [rel]

  (and
    (relation? rel)
    (every? natural-seq? rel)))

(defn numeric-nary-relation?
  [rel]

  (and
    (nary-relation? rel)
    (every? natural-seq? rel)))

(defn numeric-unary-relation?
  [rel]

  (and
    (numeric-relation? rel)
    (every? singular-seq? rel)))

(defn numeric-binary-relation?
  [rel]

  (and
    (numeric-relation? rel)
    (every? size-two-seq? rel)))

; Grid relation
(defn grid-relation
  [dimensions]

  (apply cartesian-product (map (comp set range) dimensions)))

(defn lower-triangular-relation
  [n]

  (apply
    union
    (map
      (fn [i]
        (set
          (map
            (fn [j]
              (list i j))
            (range (inc i)))))
      (range n))))

(defn upper-triangular-relation
  [n]

  (apply
    union
    (map
      (fn [i]
        (set
          (map
            (fn [j]
              (list i (+ i j)))
            (range (- n i)))))
      (range n))))

; Row and column relations
(defn row-relation
  [nth-row length]

  (set
    (map
      (fn [i]
        (list nth-row i))
      (range length))))

(defn column-relation
  [nth-column length]

  (set
    (map
      (fn [i]
        (list i nth-column))
      (range length))))

(defn main-diagonal
  [n]

  (set
    (map
      (fn [i]
        (list i i))
      (range n))))

(defn block-relation
  [start-x start-y width height]

  (set
    (cartesian-product
      (set (range start-x (+ start-x width)))
      (set (range start-y (+ start-y height))))))

(defn diagonal-relation
  [start-x start-y step-x step-y size]

  (set
    (loop [remaining size
           coll '()
           current-x start-x
           current-y start-y]
      (if (zero? remaining)
        coll
        (recur
          (dec remaining)
          (cons (list current-x current-y) coll)
          (+ current-x step-x)
          (+ current-y step-y))))))

; Block decompositions of young diagrams
; These can later be used to define young functions in terms of an input
; young coordinate system set.
(defn young-coordinate-system?
  [rel]

  (and
    (numeric-binary-relation? rel)
    (let [domain (relation-domain rel)]
      (positive-natural-range? domain)
      (every?
        (fn [i]
          (let [current-successors (direct-successors rel i)]
            (and
              (positive-natural-range? current-successors)
              (or
                (= i 1)
                (let [previous-successors (direct-successors rel (dec i))]
                  (superset? (list current-successors previous-successors)))))))
        domain))))



