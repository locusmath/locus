(ns locus.order.general.core.util
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
            [locus.order.general.core.object :refer :all]
            [locus.order.general.skeletal.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; Chain partial orders
(defn nth-chain
  [n]

  (relational-poset (apply total-order (range n))))

; Create an antichain partial order
(defn nth-antichain
  [n]

  (let [coll (set (range n))]
    (->Poset coll (coreflexive-relation coll))))

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