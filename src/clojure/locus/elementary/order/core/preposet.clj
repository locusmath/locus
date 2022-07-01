(ns locus.elementary.order.core.preposet
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]

            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]

            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)
           (locus.elementary.quiver.core.object Quiver)))

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

; Classification of preposets as semigroupoids
(derive Preposet :locus.elementary.function.core.protocols/thin-category)

; Underlying relations
(defmethod underlying-relation Preposet
  [this] (.rel this))

(defmethod visualize Preposet
  [this] (visualize (underlying-relation this)))

; Conversion routines
(defmulti to-preposet type)

(defmethod to-preposet Preposet
  [this] this)

(defmethod to-preposet Lattice
  [lattice]

  (Preposet.
    (underlying-set lattice)
    (underlying-relation lattice)))

; Convert preorders into quivers
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
(defmethod product Preposet
  [& args]

  (Preposet.
    (apply cartesian-product (map underlying-set args))
    (apply product-relation (map underlying-relation args))))

(defmethod coproduct Preposet
  [& args]

  (Preposet.
    (apply cartesian-coproduct (map underlying-set args))
    (apply sum-relation (map underlying-relation args))))

; The dual of a preordered set
(defmethod dual Preposet
  [coll]

  (Preposet. (underlying-set coll) (transpose (underlying-relation coll))))

