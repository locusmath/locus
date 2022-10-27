(ns locus.elementary.composition-quiver.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all]
            [locus.elementary.ternary-quiver.at.quiver :refer :all]
            [locus.elementary.category.core.object :refer :all]))

; The topos of composition quivers is the topos of presheaves over the compositional quiver index
; category, which is a category generated by five morphisms between three objects. Compositional
; quivers are noteworthy for providing the presheaf theoretic account of categories. They form
; a topos that includes categories as well as their immediate generalisations: semigroupoids,
; magmoids, groupoids, partial magmoids, and so on. They are so generalized that they include
; epi-mono factorisations so that by this topos you can form epi-mono factorisations of functors
; between two categories using an intermediate composition quiver determined by a quotient
; and a subobject.

; The modus operandi of Locus is to represent structures using presheaves. It is important then
; that categories, which are one of the most basic and fundamental tools in presheaf theory,
; should be represented as presheaves. The topos of compositional quivers is our fundamental
; solution. In the broadest sense it consists of multisets of composition triples of a quiver.
; Categories are then just an important special case, used to form other topoi.
(deftype CompositionQuiver [paths morphisms objects first second op source target]
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this]
    (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e]
    (list (source e) (target e))))

; Underlying multirelations of compositional quivers
(defmethod underlying-multirelation CompositionQuiver
  [^CompositionQuiver quiver]

  (multiset
    (map
      (fn [edge]
        (transition quiver edge))
      (morphisms quiver))))

(defmethod underlying-relation CompositionQuiver
  [^CompositionQuiver quiver] (set (underlying-multirelation quiver)))

(defmethod visualize CompositionQuiver
  [^CompositionQuiver quiver] (visualize (underlying-multirelation quiver)))

; Underlying path quivers of composition quivers
(defmethod paths CompositionQuiver
  [^CompositionQuiver quiver]

  (.-paths quiver))

(defmethod underlying-path-quiver CompositionQuiver
  [^CompositionQuiver quiver]

  (->PathQuiver
    (.-paths quiver)
    (.-morphisms quiver)
    (.-objects quiver)
    (.-first quiver)
    (.-second quiver)
    (.-source quiver)
    (.-target quiver)))

; Get the underlying ternary quiver of a composition quiver
(defmethod to-ternary-quiver CompositionQuiver
  [^CompositionQuiver quiver]

  (->TernaryQuiver
    (.-paths quiver)
    (.-morphisms quiver)
    (.-first quiver)
    (.-second quiver)
    (.-op quiver)))

; Ontology of compositional quivers
(defn composition-quiver?
  [quiver]

  (= (type quiver) CompositionQuiver))