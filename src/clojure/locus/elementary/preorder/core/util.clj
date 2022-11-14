(ns locus.elementary.preorder.core.util
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.order.core.object :refer :all]))

; Create an antichain partial order
(defn nth-antichain
  [n]

  (let [coll (set (range n))]
    (->Poset coll (coreflexive-relation coll))))

(defn nth-chain
  [n]

  (relational-poset (apply total-order (range n))))

(defn nth-complete-preorder
  [n]

  (relational-preposet (complete-relation (set (range n)))))

(defn n-pair-order
  [n]

  (->Poset
    (->RangeSet 0 (* 2 n))
    (union
      (set
        (map
          (fn [i]
            (list i i))
          (range (* 2 n))))
      (set
        (map
          (fn [i]
            (list (* 2 i) (inc (* 2 i))))
          (range n))))))

(defn unordered-n-pair-preorder
  [n]

  (->Poset
    (->RangeSet 0 (* 2 n))
    (apply
      union
      (map
        (fn [i]
          #{(list i i)
            (list (inc i) (inc i))
            (list i (inc i))
            (list (inc i) i)})
        (range 0 (* 2 n) 2)))))

(defn nth-higher-diamond-order
  [n]

  (relational-poset
    (weak-order
      [#{0} (set (range 1 (inc n))) #{(inc n)}])))