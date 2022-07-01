(ns locus.elementary.logic.base.hyper
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.sig :refer :all]))

; Let (N,*) be the commutative monoid of natural numbers, then this commutative monoid naturally
; separates each element of N into isomorphism classes, defined as the orbits of its automorphism
; group. These isomorphism classes are simply the prime signatures. As an equivalence relation,
; the partition of the natural numbers by prime signature does not form a congruence, and therefore
; it doesn't have a well defined monoid quotient. To get around this, we define a quotient
; hyperoperation of natural numbers by prime signatures. This hyperoperation then resolves the question
; of what prime signature classes a number can be in that is the product of two separate numbers of
; different prime signatures. As this does not come any previous source, we provide a original
; and independently developed implementation that is a result of our own research.

; Hypermultiplication of additive partitions
(defn multiset-couplings
  [a b]

  (if (or (empty? a) (empty? b))
    #{(multiset '())}
    (let [current-elem (first (support a))
          current-multiplicity (multiplicity a current-elem)]
      (apply
       union
       (map
        (fn [current-selection]
          (set
            (map
              (fn [current-coupling]
              (add
               current-coupling
               (multiset
                (map
                 (fn [i]
                   (list current-elem i))
                 current-selection))))
              (multiset-couplings
                (completely-remove-multiset-element a current-elem)
                (multiset-difference b current-selection)))))
        (multiset-selections b current-multiplicity))))))

(defn multiply-partitions
  [a b]

  (set
   (map
    (fn [current-coupling]
      (multiset
       (for [i current-coupling
             :let [n (apply + i)]
             :when (not (zero? n))]
         n)))
    (multiset-couplings
     (add a (repeat-multiset (count b) 0))
     (add b (repeat-multiset (count a) 0))))))

; Signature embeddings
(defn special-sorting
  [coll]

  (map
   (fn [i]
     [i (multiplicity coll i)])
   (sort > (support coll))))

(defn se
  [parent-signature sorted-map]

  (if (empty? sorted-map)
    #{#{}}
    (let [[current-elem current-multiplicity] (first sorted-map)
          filtered-parent (multiset
                           (filter
                            (fn [i]
                              (<= current-elem i))
                            parent-signature))
          current-selections (multiset-selections
                              filtered-parent
                              current-multiplicity)]
      (mapcat
       (fn [selection]
         (map
          (fn [rel]
            (add
             rel
             (multiset
              (map
               (fn [i]
                 (list i current-elem))
               selection))))
          (se (multiset-difference parent-signature selection)
              (rest sorted-map))))
       current-selections))))

(defn signature-embeddings
  [parent-signature subsignature]

  (se parent-signature
      (special-sorting subsignature)))

(defn divide-partitions
  [parent-partition child-partition]

  (set
   (map
    (fn [rel]
      (multiset
       (for [[b a] rel
             :let [diff (- b a)]
             :when (not (zero? diff))]
         diff)))
    (signature-embeddings
     parent-partition
     (let [cardinality-difference (- (count parent-partition)
                                     (count child-partition))]
       (add child-partition (repeat-multiset cardinality-difference 0)))))))
