(ns locus.elementary.order.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.preorder.core.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)))

; In our categorical framework, a Poset is simply a skeletal thin category. Although most of the
; details of Posets are described by thin categories, some multimethods behave differently
; when operating on Posets instead of thin categories.

(deftype Poset [coll rel]
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
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Classification of posets
(derive Poset :locus.elementary.copresheaf.core.protocols/thin-skeletal-category)

; Underlying relation and visualize multimethods
(defmethod underlying-relation Poset
  [this]

  (->SeqableRelation (.-coll this) (.-rel this) {}))

(defmethod visualize Poset
  [this] (visualize (covering-relation (underlying-relation this))))

; Relational posets
(defn relational-poset
  [rel]

  (Poset.
    (vertices rel)
    rel))

; Conversion multimethods
(defmulti to-poset type)

(defmethod to-poset Poset
  [obj] obj)

(defmethod to-poset Quiver
  [quiv]

  (Poset.
    (objects quiv)
    (underlying-relation quiv)))

(defmethod to-poset :default
  [rel]

  (relational-poset rel))

; We also need special routines for products and coproducts
(defmethod product Poset
  [& args]

  (Poset.
    (apply cartesian-product (map underlying-set args))
    (apply product-relation (map underlying-relation args))))

(defmethod coproduct Poset
  [& args]

  (Poset.
    (apply cartesian-coproduct (map underlying-set args))
    (apply sum-relation (map underlying-relation args))))

; The dual of a preordered set
(defmethod dual Poset
  [coll]

  (Poset. (underlying-set coll) (transpose (underlying-relation coll))))

; Special types of partial orders on common sets
(defn partitions-poset
  [coll]

  (Poset.
    (set coll)
    (binary-subrelation set-superpartition? coll)))

(defn discrete-poset
  [coll]

  (Poset. (set coll) (coreflexive-relation coll)))

; Convert common types of collections directly into partial orders
(defn as-poset
  [coll]

  (Poset.
    (set coll)
    (if (empty? coll)
      #{}
      (let [selected-element (first coll)]
        (cond
          (number? selected-element) (binary-subrelation superrational? coll)
          (seq? selected-element) (binary-subrelation supersequence? coll)
          (multiset? selected-element) (binary-subrelation superbag? coll)
          (set-function? selected-element) (binary-subrelation superfunction? coll))))))
