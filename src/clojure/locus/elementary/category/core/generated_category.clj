(ns locus.elementary.category.core.generated-category
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.relation.set-relation :refer :all]
            [locus.elementary.order.core.object :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.preorder.setoid.object :refer :all]))

; A generated category is a category with a specifically specified morphic generating set.
; This is useful because it allows us to specify the data of a category, without having
; to worry about how to handle all of its morphisms, because we can concern ourselves
; simply with the generating set. In particular, this is useful when defining presheaves.
(deftype GeneratedCategory [morphisms objects source target func id gens]
  ; Generated categories are structured quivers
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (id obj))
  (underlying-unital-quiver [this] (->UnitalQuiver morphisms objects source target id))

  ; Generated categories are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Generated categories are part of the ontology of categories
(derive GeneratedCategory :locus.elementary.copresheaf.core.protocols/category)

; Define a method that integrates the generated category class into our overall system
; for dealing with morphic generating sets of categories
(defmethod morphic-gens GeneratedCategory
  [^GeneratedCategory category]

  (.gens category))

; Add on a morphic generating set to an existing category
(defn adjoin-generators
  [category gens]

  (->GeneratedCategory
    (morphisms category)
    (objects category)
    (source-fn category)
    (target-fn category)
    (fn [[a b]]
      (category (list a b)))
    (fn [a]
      (identity-morphism-of category a))
    gens))

; Let P be a finite poset then the covering relation of P provides for a valid
; morphic generating set of P.
(defn covering-generated-category
  ([edges]
   (covering-generated-category (vertices edges) edges))
  ([vertices edges]

   (->GeneratedCategory
     edges
     vertices
     first
     second
     compose-ordered-pairs
     (fn [x] (list x x))
     (covering-relation edges))))





