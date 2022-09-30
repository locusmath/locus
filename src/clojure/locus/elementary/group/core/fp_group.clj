(ns locus.elementary.group.core.fp-group
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.numeric.np :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]))

; Finitely presented groups
; A finitely presented group is determined by a set of generators as well
; as a set of relators. Relators are generators for the normal subgroup
; of the presentation of the group, and they are dual to and determine relations
; by equating each relator to zero.

(deftype FPGroup [n relators])

(derive FPGroup :locus.elementary.copresheaf.core.protocols/group)

(defmethod morphic-gens FPGroup
  [^FPGroup group]

  (let [n (inc (.n group))]
    (union (set (range 1 n))
           (set (range -1 (- n) -1)))))

; Get the commutator term of a finitely presented group
(defn commutator-relator
  [a b]

  [a b (- a) (- b)])

; Create commutativity relations in groups
(defn commutativity-relations
  [i]

  (let [n (inc i)
        coll (set (range 1 n))]
    (map
      (fn [pair]
        (let [[a b] (seq pair)]
          [a b (- a) (- b)]))
      (selections coll 2))))

(defn free-fp-group
  [n]

  (FPGroup. n []))

(defn free-commutative-fp-group
  [n]

  (FPGroup. n (commutativity-relations n)))

; Baumslag-Solitar group
(defn bs
  [m n]

  (FPGroup.
    2
    [(concat
       (list 2)
       (repeat (int (Math/abs m)) (if (pos? m) 1 -1))
       (list -2)
       (repeat (int (Math/abs n)) (if (pos? n) -1 1)))]))

; A finitely presented one relator group
(defn torus-knot-group
  [p q]
  {:pre (coprime-positive-integers? (list p q))}

  (FPGroup.
    2
    [(concat (repeat p 1) (repeat q -1))]))

; Baumslag Gersten group
(defn bg
  [a t]

  (FPGroup.
    2
    [-2 -1 2 1 -2 1 2 -1 -1]))

; oriented surface groups by commutators
(defn oriented-surface-group
  [n]

  (FPGroup.
    (* 2 n)
    (mapcat
      (fn [i]
        (commutator-relator
          (+ (* 2 i) 1)
          (+ (* 2 i) 2)))
      (range n))))

; a non-oriented surface group
(defn nonoriented-surface-group
  [n]

  (FPGroup.
    n
    [(mapcat
       (fn [i]
         (list i i))
       (range 1 (inc n)))]))

; Create a coxeter group from a coxeter matrix
(defn coxeter-group
  [matrix]

  (let [n (count matrix)]
    (FPGroup.
      n
      (for [i (range n)
            j (range n)
            :let [pow (nth (nth matrix i) j)]
            :when (not= pow Double/POSITIVE_INFINITY)]
        (apply
          concat
          (repeat
            pow
            (list (inc i) (inc j))))))))

(defn cyclic-fp-group
  [n]

  (FPGroup.
    1
    [(repeat n 1)]))

(defn dihedral-fp-group
  [n]

  (FPGroup.
    2
    [(repeat n 1)
     (list 2 2)
     (list 1 2 1 2)]))

(defn dicyclic-fp-group
  [n]

  (FPGroup.
    2
    [(repeat (* 2 n) 1)
     (concat (repeat n 1) (list 2 2))
     (list 2 1 -2 1)]))

(def infinite-dihedral-group
  (FPGroup.
    2
    [(list 2 2)
     (list 1 2 1 2)]))

; Braid groups
(defn braid-group
  [n]

  (FPGroup.
    n
    (concat
      (for [i (range 1 (inc n))
            j (range 1 (inc n))
            :when (and
                    (not= i j)
                    (not= j (inc i))
                    (not= j (dec i)))]
        (commutator-relator i j))
      (map
        (fn [i]
          [i (inc i) i (- (inc i)) (- i) (- (inc i))])
        (range 1 n)))))

(defn symmetric-fp-group
  [n]

  (let [temp (braid-group n)]
    (FPGroup.
      n
      (concat
        (.relators temp)
        (map
          (fn [i]
            (list i i))
          (range 1 (inc n)))))))

(defn symmetric-coxeter-matrix
  [n]

  (map
    (fn [y]
      (map
        (fn [x]
          (cond
            (= x y) 1
            (= 1 (int (Math/abs (- x y)))) 3
            :else 2))
        (range 1 (inc n))))
    (range 1 (inc n))))

(defn symmetric-coxeter-group
  [n]

  (coxeter-group (symmetric-coxeter-matrix n)))

; Some finite groups defined by presentations
(def klein-four-fp-group
  (FPGroup.
    2
    [[1 1]
     [2 2]
     [1 2 1 2]]))

(def tetrahedral-fp-group
  (FPGroup.
    2
    [[1 1]
     [2 2 2]
     [1 2 1 2 1 2]]))

(def octahedral-fp-group
  (FPGroup.
    2
    [[1 1]
     [2 2 2]
     [1 2 1 2 1 2 1 2]]))

(def icosahedral-fp-group
  (FPGroup.
    2
    [[1 1]
     [2 2 2]
     [1 2 1 2 1 2 1 2 1 2]]))

(def quaternion-fp-group
  (FPGroup.
    2
    [[1 1 1 1]
     [2 1 2 -1]
     [1 2 1 -2]]))



