(ns locus.elementary.order.core.poset
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.funpair :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)
           (locus.elementary.lattice.core.object Lattice)))

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
(derive Poset :locus.elementary.function.core.protocols/thin-category)

; Underlying relations
(defmethod underlying-relation Poset
  [this] (.rel this))

(defmethod visualize Poset
  [this] (visualize (covering-relation (underlying-relation this))))

; Conversion routines
(defmulti to-poset type)

(defmethod to-poset Poset
  [poset] poset)

(defmethod to-poset Lattice
  [lattice]

  (Poset.
    (underlying-set lattice)
    (underlying-relation lattice)))

; Converting quivers into posets
(defmethod to-poset Quiver
  [quiv]

  (Poset.
    (objects quiv)
    (underlying-relation quiv)))

; Relational posets
(defn relational-poset
  [rel]

  (Poset.
    (vertices rel)
    rel))

(defmethod to-poset :default
  [rel]

  (relational-poset rel))

; We also need special routines for
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

; This function lets us create posets from arbitrary collections
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
          (set-function? selected-element) (binary-subrelation superfunction? coll)
          (diset? selected-element) (binary-subrelation superdiset? coll))))))

(defn partitions-poset
  [coll]

  (Poset.
    (set coll)
    (binary-subrelation set-superpartition? coll)))

; Extra functionality for creating and dealing with posets
(defn discrete-poset
  [coll]

  (Poset. (set coll) (coreflexive-relation coll)))

