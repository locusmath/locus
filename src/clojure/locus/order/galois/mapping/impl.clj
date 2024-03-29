(ns locus.order.galois.mapping.impl
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

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

(derive ResiduatedMapping :locus.set.copresheaf.structure.core.protocols/monotone-map)

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

(derive CoresiduatedMapping :locus.set.copresheaf.structure.core.protocols/monotone-map)

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