(ns locus.order.general.skeletal.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

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
(derive Poset :locus.set.copresheaf.structure.core.protocols/thin-skeletal-category)

; Underlying relation and visualize multimethods
(defmethod underlying-relation Poset
  [this]

  (->SeqableRelation (.-coll this) (.-rel this) {}))

; Relational posets
(defn relational-poset
  [rel]

  (Poset.
    (vertices rel)
    rel))

; Take a thin category and get a partial order from it by condensation
(defn condensation-poset
  [preposet]

  (let [rel (underlying-relation preposet)
        partition (strong-connectivity rel)]
    (->Poset
      partition
      (relation-quotient rel partition))))

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

; This is a way of getting the lexicographic of two posets
(defn lexicographic-product-order
  [p1 p2]

  (let [r1 (underlying-relation p1)
        r2 (underlying-relation p2)]
    (->Poset
     (product (objects p1) (objects p2))
     (fn [[x1 y1] [x2 y2]]
       (or
         (r1 (list x1 x2))
         (and
           (= x1 x2)
           (r2 (list y1 y2))))))))

(defn linear-sum
  [& posets]

  (->Poset
    (apply cartesian-coproduct (map objects posets))
    (fn [[i v1] [j v2]]
      (or
        (<= i j)
        (and
          (= i j)
          (let [r (underlying-relation (nth posets i))]
            (r (list v1 v2))))))))

; Suborders of partial orders
(defn subposet
  [poset new-objects new-morphisms]

  (->Poset new-objects new-morphisms))

(defn wide-subposet
  [poset new-morphisms]

  (subposet poset (objects poset) new-morphisms))

(defn full-subposet
  [poset new-objects]

  (->Poset
    new-objects
    (subrelation (underlying-relation poset) new-objects)))
