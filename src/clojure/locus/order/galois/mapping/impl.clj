(ns locus.order.galois.mapping.impl
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]))

; Let F: A -> B and G: B -> A together be a Galois connection of preorders. Then the lower
; adjoint of this  Galois connection is a residuated mapping and the upper adjoint is a
; coresiduated mapping, and either of these objects presented by themselves is enough
; to reconstruct the entire adjunction. A residuated mapping is also defined as a
; monotone map that reflects principal idelas.
(deftype ResiduatedMapping [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction (morphisms source) (morphisms target) (partial map func)))
  (second-function [this]
    (->SetFunction (objects source) (objects target) func))

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive ResiduatedMapping :locus.elementary.copresheaf.core.protocols/monotone-map)

(defmulti to-residuated-mapping type)

(defmethod to-residuated-mapping ResiduatedMapping
  [^ResiduatedMapping mapping] mapping)

; The dual concept of a residuated mapping is a coresiduated mapping. While a residuated mapping
; is a monotone map that reflects principal ideals, a coresiduated mapping is a monotone map
; that reflects principal filters. The category of Galois connection can be represented either
; in terms of the category of orders and residuated mappings or in terms of the category of
; orders and coresiduated mappings.
(deftype CoresiduatedMapping [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction (morphisms source) (morphisms target) (partial map func)))
  (second-function [this]
    (->SetFunction (objects source) (objects target) func))

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive CoresiduatedMapping :locus.elementary.copresheaf.core.protocols/monotone-map)

(defmulti to-coresiduated-mapping type)

(defmethod to-coresiduated-mapping CoresiduatedMapping
  [^CoresiduatedMapping mapping] mapping)

; Residuated and coresiduated mappings both form categories
(defmethod compose* ResiduatedMapping
  [^ResiduatedMapping a, ^ResiduatedMapping b]

  (->ResiduatedMapping
    (source-object b)
    (target-object a)
    (comp (.-func a) (.-func b))))

(defmethod compose* CoresiduatedMapping
  [^CoresiduatedMapping a, ^CoresiduatedMapping b]

  (->CoresiduatedMapping
    (source-object b)
    (target-object a)
    (comp (.-func a) (.-func b))))

; The other adjoints of a residuated mapping or a coresiduated mapping can be uniquely determined
(defn residual
  [mapping]

  (let [source-relation (underlying-relation (source-object mapping))]
    (->CoresiduatedMapping
     (target-object mapping)
     (source-object mapping)
     (fn [i]
       (first (maximal-member-vertices source-relation (reflect-principal-ideal mapping i)))))))

(defn coresidual
  [mapping]

  (let [source-relation (underlying-relation (source-object mapping))]
    (->ResiduatedMapping
      (target-object mapping)
      (source-object mapping)
      (fn [i]
        (first (minimal-member-vertices source-relation (reflect-principal-filter mapping i)))))))

; Ontology of residuated and coresiduated mappingss
(defmethod residuated-mapping? ResiduatedMapping
  [^ResiduatedMapping mapping] true)

(defmethod coresiduated-mapping? CoresiduatedMapping
  [^CoresiduatedMapping mapping] true)