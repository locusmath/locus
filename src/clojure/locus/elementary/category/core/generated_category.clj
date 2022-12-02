(ns locus.elementary.category.core.generated-category
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.vertices :refer :all]
            [locus.quiver.diset.core.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.thin.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.skeletal.object :refer :all]
            [locus.order.general.symmetric.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all]))

; A generated category is a category with a specifically specified morphic generating set.
; This is useful because it allows us to specify the data of a category, without having
; to worry about how to handle all of its morphisms, because we can concern ourselves
; simply with the generating set. In particular, this is useful when defining presheaves.
(deftype GeneratedCategory [quiver op gens]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] (underlying-quiver quiver))
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (identity-morphism-of quiver obj))
  (underlying-unital-quiver [this] quiver)

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms quiver))

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Generated categories are part of the ontology of categories
(derive GeneratedCategory :locus.elementary.copresheaf.core.protocols/category)

; Define a method that integrates the generated category class into our overall system
; for dealing with morphic generating sets of categories
(defmethod morphic-gens GeneratedCategory
  [^GeneratedCategory category]

  (.gens category))

; Adjoin generators to a category
(defn adjoin-generators
  [category gens]

  (->GeneratedCategory
    (underlying-unital-quiver category)
    (fn [[a b]]
      (category (list a b)))
    gens))

; Let P be a finite poset then the covering relation of P provides for a valid
; morphic generating set of P.
(defn covering-generated-category
  ([edges]
   (covering-generated-category (vertices edges) edges))
  ([vertices edges]
   (->GeneratedCategory
     (relational-unital-quiver vertices edges)
     compose-ordered-pairs
     (covering-relation edges))))


