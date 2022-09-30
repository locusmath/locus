(ns locus.elementary.relation.ternary.tr
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.relation.ternary.op :refer :all]))

; A ternary relation is a set of ordered triples.
; The theory of ternary relations is less known than the theory of binary relations.
; However, a number of important classes of ternary relations are well known and
; have been explored such as cyclic ordering relations, betweenness relations,
; and binary operations expressed as ternary relations.

; Complete ternary relations
(defn complete-ternary-relation
  [coll]

  (cartesian-power coll 3))

(defn complete-ternary-relation?
  [rel]

  (and
    (relation? rel)
    (equal-universals? rel (complete-ternary-relation (vertices rel)))))

; Moore families of ternary relations
(def front-symmetric-ternary-relation?
  (moore-family
   size-three-seq?
   (fn [rel]
     (union
      rel
      (set
       (map
        (fn [i]
          (list (nth i 1) (nth i 0) (nth i 2)))
        rel))))))

(def back-symmetric-ternary-relation?
  (moore-family
   size-three-seq?
   (fn [rel]
     (union
      rel
      (set
       (map
        (fn [i]
          (list (nth i 0) (nth i 2) (nth i 1)))
        rel))))))

(def outer-symmetric-ternary-relation?
  (moore-family
   size-three-seq?
   (fn [rel]
     (union
      rel
      (set
       (map
        (fn [i]
          (list (nth i 2) (nth i 1) (nth i 0)))
        rel))))))

(def cyclic-ternary-relation?
  (moore-family
   size-three-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (map
        (fn [i]
          #{(list (nth i 1) (nth i 2) (nth i 0))
            (list (nth i 2) (nth i 0) (nth i 1))})
        rel))))))

(def fully-symmetric-ternary-relation?
  (moore-family
   size-three-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (map
        (fn [i]
          #{(list (nth i 0) (nth i 2) (nth i 1))
            (list (nth i 1) (nth i 0) (nth i 2))
            (list (nth i 1) (nth i 2) (nth i 0))
            (list (nth i 2) (nth i 0) (nth i 1))
            (list (nth i 2) (nth i 1) (nth i 0))})
        rel))))))

; Set systems related to betweenness
(defn betweenness-intervals
  [rel]

  (let [coll (vertices rel)]
    (union
     #{#{}}
     (selections coll 1)
     (set
      (map
       (fn [pair]
         (set
          (for [[a b c] rel
                :when (= (set (list a c)) pair)]
            b)))
       (selections coll 2))))))

; Outer symmetric ternary relations
(defn betweenness-relation
  [order]

  (intersection
   (cartesian-product
    (vertices order)
    (vertices order)
    (vertices order))
   (fn [[x y z]]
     (or
      (and
       (order [x y])
       (order [y z]))
      (and
       (order [z y])
       (order [y x]))))))

(defn betweenness-comparability
  [rel]
  
  (let [coll (vertices rel)]
    (intersection
     (fn [[a b]]
       (not
        (every?
         (complement
          (fn [i]
            (rel (list a i b))))
         coll)))
     (cartesian-product coll coll))))

(def partial-betweenness-relation?
  (intersection
   (power-set
    (fn [edge]
      (and
       (size-three-seq? edge)
       (or
        (equal-seq? edge)
        (not= (first edge) (last edge))))))
    (fn [rel]
      (every?
       (fn [[[a b c] [d e f]]]
         (or
          (not (= b d))
          (rel (list c b e))
          (rel (list f b a))))
       (cartesian-product rel rel)))))

(def betweenness-relation?
  (intersection
   partial-betweenness-relation?
   (fn [rel]
     (let [coll (vertices rel)]
       (every?
        (fn [[a b c]]
          (or
           (not
            (and
             (rel (list a a c))
             (rel (list b b c))
             (rel (list c c a))))
           (rel (list a b c))
           (rel (list b c a))
           (rel (list c a b))))
        (cartesian-product coll coll coll))))))

(def acyclic-betweenness-relation?
  (intersection
   betweenness-relation?
   (fn [rel]
     (= (intersection
         (multiselection entity? #{1 2})
         (cl subclass-closed? (betweenness-intervals rel)))
        (set
         (map
          (fn [[a b c]]
            (set (list a c)))
          rel))))))

(def total-partial-betweenness-relation?
  (intersection
   partial-betweenness-relation?
   (comp anticoreflexive? betweenness-comparability)))

(def total-betweenness-relation?
  (intersection
   betweenness-relation?
   (comp anticoreflexive? betweenness-comparability)))

; Cyclic relations
(def cyclic-preordering-relation?
  (moore-family
   size-three-seq?
   (fn [rel]
     (let [cyclic-closure (apply
                           union
                           (map
                            (fn [[a b c]]
                              (set
                               (list
                                (list a b c)
                                (list c a b)
                                (list b c a))))
                            rel))]
       (letfn [(transitive-closure [rel]
                 (let [coll (vertices rel)
                       new-rel (union
                                rel
                                (apply
                                 union
                                 (for [[a b c d] (cartesian-product coll coll coll coll)
                                       :when (and
                                              (rel (list a b c))
                                              (rel (list a c d)))]
                                   (set
                                    (list
                                     (list a b d)
                                     (list d a b)
                                     (list b d a))))))]
                   (if (= rel new-rel)
                     rel
                     (transitive-closure new-rel))))]
         (transitive-closure cyclic-closure))))))

(def cyclic-ordering-relation?
  (intersection
    cyclic-preordering-relation?
    (fn [rel]
     (every?
      (fn [[a b c]]
        (not (rel (list c b a))))
      rel))))

(def total-cyclic-ordering-relation?
  (intersection
    cyclic-ordering-relation?
    (fn [rel]
     (let [coll (vertices rel)]
       (every?
        (fn [[a b c]]
          (or
           (not (distinct? a b c))
           (rel (list a b c))
           (rel (list c b a))))
        (cartesian-product coll coll coll))))))

; Ternary multirelations
(defn ternary-multirelation?
  [rel]

  (and
    (multiset? rel)
    (every? size-three-seq? rel)))

(defn equal-ternary-multirelation?
  [rel]

  (and
    (equal-multiset? rel)
    (every? size-three-seq? rel)))
