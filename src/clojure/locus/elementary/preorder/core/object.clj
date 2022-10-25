(ns locus.elementary.preorder.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.order.core.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)))

; In the category of categories Cat, we have to provide special consideration for thin categories
; because the category of thin categories is a concrete category with a forgetful functor
; to its object set. A thin category is essentially a category for which the composition
; operation of the category is trivial, so the morphism part of a functor of thin
; categories can be inferred entirely from the object part.
(deftype Preposet [coll rel]
  ConcreteObject
  (underlying-set [this] coll)

  ; Structured quivers
  StructuredDiset
  (first-set [this] rel)
  (second-set [this] coll)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver rel coll first second))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver rel coll first second (fn [x] (list x x))))
  (identity-morphism-of [this x]
    (list x x))

  ; Every thin category is a function
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] rel)

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]]
    (list c b))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Preposet :locus.elementary.copresheaf.core.protocols/thin-category)

; Underlying relations
(defmethod underlying-relation Preposet
  [this] (.rel this))

(defmethod visualize Preposet
  [this] (visualize (underlying-relation this)))

; Conversion routines
(defmulti to-preposet type)

(defmethod to-preposet Preposet
  [this] this)

(defmethod to-preposet Quiver
  [quiv]

  (Preposet.
    (objects quiv)
    (underlying-relation quiv)))

; Relational preposets
(defn relational-preposet
  [rel]

  (Preposet. (vertices rel) rel))

(defmethod to-preposet :default
  [rel]

  (relational-preposet rel))

; We also need special routines for
(defmethod product :locus.elementary.copresheaf.core.protocols/thin-category
  [& args]

  (Preposet.
    (apply cartesian-product (map underlying-set args))
    (apply product-relation (map underlying-relation args))))

(defmethod coproduct :locus.elementary.copresheaf.core.protocols/thin-category
  [& args]

  (Preposet.
    (apply cartesian-coproduct (map underlying-set args))
    (apply sum-relation (map underlying-relation args))))

; The dual of a preordered set
(defmethod dual Preposet
  [coll]

  (Preposet. (underlying-set coll) (transpose (underlying-relation coll))))

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
