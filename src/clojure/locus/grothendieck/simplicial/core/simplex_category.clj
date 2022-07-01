(ns locus.grothendieck.simplicial.core.simplex-category
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.grothendieck.simplicial.core.simplicial-morphism :refer :all]))

; Let us suppose that /_\ is the simplex category. Then its corresponding presheaf topos
; is the topos of simplicial sets. This topos is mainly used in homotopy theory and
; applications in geometry, so we make not of how it is closely linked to topology.
; The simplex category is not finitely generated.

; A singleton class that uniquely defines the simplex category.
(deftype SimplexCategory []
  ; Categories are structured quivers
  StructuredDiset
  (first-set [this] simplicial-morphism?)
  (second-set [this] positive-integer?)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver simplicial-morphism? positive-integer? source-object target-object))
  (source-fn [this] source-object)
  (target-fn [this] target-object)
  (transition [this e] (list (source-object e) (target-object e)))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver simplicial-morphism? positive-integer? source-object target-object identity-morphism))
  (identity-morphism-of [this obj]
    (simplicial-identity-morphism obj))

  ; Categories are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] simplicial-morphism?)

  clojure.lang.IFn
  (invoke [this [a b]] (compose a b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ; Make it so that the simplex category is displayed in a special manner
  java.lang.Object
  (toString [this] "Δ")
  (equals [this x] (instance? SimplexCategory x)))

(derive SimplexCategory :locus.elementary.function.core.protocols/concrete-category)

(defmethod print-method SimplexCategory [^SimplexCategory v, ^java.io.Writer w]
  (.write w (.toString v)))

(def simplex-category
  (SimplexCategory.))

; A singleton class that uniquely defines the cosimplex category.
(deftype CosimplexCategory []
  ; Categories are structured quivers
  StructuredDiset
  (first-set [this] simplicial-morphism?)
  (second-set [this] positive-integer?)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver simplicial-morphism? positive-integer? target-object source-object))
  (source-fn [this] target-object)
  (target-fn [this] source-object)
  (transition [this e] (list (target-object e) (source-object e)))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver simplicial-morphism? positive-integer? target-object source-object identity-morphism))
  (identity-morphism-of [this obj]
    (simplicial-identity-morphism obj))

  ; Categories are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] simplicial-morphism?)

  clojure.lang.IFn
  (invoke [this [a b]] (compose b a))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ; Make it so that the simplex category is displayed in a special manner
  java.lang.Object
  (toString [this] "Δ*")
  (equals [this x] (instance? CosimplexCategory x)))

(derive CosimplexCategory :locus.elementary.function.core.protocols/concrete-category)

(defmethod print-method CosimplexCategory [^CosimplexCategory v, ^java.io.Writer w]
  (.write w (.toString v)))

(def cosimplex-category
  (CosimplexCategory.))

; The simplex and cosimplex categories are duals of one another
(defmethod dual SimplexCategory
  [category] cosimplex-category)

(defmethod dual CosimplexCategory
  [category] simplex-category)



