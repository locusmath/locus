(ns locus.magmoid.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]))

; Magmoids are non-associative generalisations of categories
(deftype Magmoid [morphisms objects source target func]
  ; Semigroupoids are structured quivers
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  ; Semigroupoids are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Ontology of magmoids
(defn magmoid?
  [obj]

  (= (type obj) Magmoid))