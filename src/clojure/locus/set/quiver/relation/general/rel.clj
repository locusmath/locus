(ns locus.set.quiver.relation.general.rel
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]))

; Classes of relations defined by cardinality
(def singular-relation?
  (intersection
    relation?
    singular-universal?))

(def size-two-relation?
  (intersection
    relation?
    size-two-universal?))

(def size-three-relation?
  (intersection
    relation?
    size-three-universal?))

(def size-four-relation?
  (intersection
    relation?
    size-four-universal?))

; Classes of relations defined by arity
(def nullfree-relation?
  (power-set (intersection seq? (complement empty?))))

(defn rank-one-relation?
  [rel]

  (every?
   (fn [i]
     (<= (count i) 1))
   rel))

(defn rank-two-relation?
  [rel]

  (every?
   (fn [i]
     (<= (count i) 2))
   rel))

(def nullfree-rank-two-relation?
  (intersection
   nullfree-relation?
   rank-two-relation?))

(defn rank-three-relation?
  [rel]

  (every?
   (fn [i]
     (<= (count i) 3))
   rel))

(def nullfree-rank-three-relation?
  (intersection
   nullfree-relation?
   rank-three-relation?))

(defn rank-four-relation?
  [rel]

  (every?
   (fn [i]
     (<= (count i) 4))
   rel))

(def nullfree-rank-four-relation?
  (intersection
   nullfree-relation?
   rank-four-relation?))

; Fully antisymmetric relation
(defn fully-antisymmetric-relation?
  [rel]

  (and
    (relation? rel)
    (or
      (= (count rel) 0)
      (apply distinct? (map multiset rel)))))

; Equal and distinct sequences
(def totally-distinct-relation?
  (power-set distinct-seq?))

(def totally-disconnected-relation?
  (power-set equal-seq?))

; Monotone sequences
(defn monotone-sequences
  [rel]

  (letfn [(monotone-sequences* [rel current-coll]
            (let [current-elem (last current-coll)
                  next-elems (disj (successors rel current-elem) current-elem)]
              (if (empty? next-elems)
                #{current-coll}
                (union
                 #{current-coll}
                 (apply
                  union
                  (map
                   (fn [i]
                     (monotone-sequences* rel (concat current-coll (list i))))
                   next-elems))))))]
    (conj
     (apply
      union
      (map
       (fn [i]
         (monotone-sequences* rel (list i)))
       (vertices rel)))
     (list))))

; Permutations
(def permutation?
  (forwards-relation
    (fn [[a b]]
      (contains? (enumerate-sequence-permutations a) b))
    (fn [a]
      (enumerate-sequence-permutations a))))

(def fully-symmetric-relation?
  (moore-family
    seq?
    (fn [rel]
      (union
        rel
        (apply union (map (fn [i] (enumerate-sequence-permutations i)) rel))))))

; Subsequence based relations
(def subsequence-closed-relation?
  (moore-family
    seq?
    (fn [rel]
      (union
        rel
        (apply
          union
          (map
            (fn [i]
              (direct-predecessors index-promotion? i))
            rel))))))

(defn subsequence-free-relation?
  [rel]

  (and
    (relation? rel)
    (every?
      (fn [[a b]]
        (or
          (= a b)
          (not (index-promotion? (list a b)))))
      (cartesian-product rel rel))))




