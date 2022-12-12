(ns locus.set.copresheaf.topoi.concrete-quiver.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]))

; A concrete quiver is the same thing as a copresheaf F: Free(Q) -> Sets, from the free
; category of a quiver to the topos of Sets.

(deftype ConcreteQuiver [quiver morphism-function object-function]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] quiver)
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  ConcreteCategoricalStructure
  (object-to-set [this x]
    (object-function x))
  (morphism-to-function [this x]
    (morphism-function x)))

(derive ConcreteQuiver :locus.set.copresheaf.structure.core.protocols/structured-quiver)

; Create a concrete quiver from a function system
(defn concrete-quiver
  ([sets functions]
   (->ConcreteQuiver
     (->Quiver
       functions
       sets
       inputs
       outputs)
     identity
     identity))
  ([functions]
   (concrete-quiver
     (set
       (mapcat
         (fn [function]
           (list (inputs function) (outputs function)))
         functions))
     functions)))

; Convert a concrete quiver into a copresheaf over a free category
(defmethod to-copresheaf ConcreteQuiver
  [^ConcreteQuiver quiver]

  (free-copresheaf
    (.-quiver quiver)
    (.-morphism_function quiver)
    (.-object_function quiver)))

; Multimethods for quivers
(defmethod underlying-relation ConcreteQuiver
  [^ConcreteQuiver quiver] (underlying-relation (.-quiver quiver)))

(defmethod underlying-multirelation ConcreteQuiver
  [^ConcreteQuiver quiver] (underlying-multirelation (.-quiver quiver)))

(defmethod visualize ConcreteQuiver
  [^ConcreteQuiver quiver] (visualize (.-quiver quiver)))

; Ontology of concrete quivers
(defn concrete-quiver?
  [quiver]

  (= (type quiver) ConcreteQuiver))
