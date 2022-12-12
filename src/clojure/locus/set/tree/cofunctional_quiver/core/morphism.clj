(ns locus.set.tree.cofunctional-quiver.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all]
            [locus.set.tree.cofunctional-quiver.core.object :refer :all])
  (:import (locus.set.tree.cofunctional_quiver.core.object CofunctionalQuiver)))

; A morphism in the topos of cofunctional quivers is a natural transformation of the cofunctional quivers
; represented as presheaves.
(deftype MorphismOfCofunctionalQuivers [source target morphism-function object-function out-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive MorphismOfCofunctionalQuivers :locus.set.logic.structure.protocols/morphism-of-copresheaves)

; Identities and compositoin in the topos of cofunctional quivers
(defmethod identity-morphism CofunctionalQuiver
  [^CofunctionalQuiver quiver]

  (->MorphismOfCofunctionalQuivers quiver quiver identity identity identity))

(defmethod compose MorphismOfCofunctionalQuivers
  [f g]

  (->MorphismOfCofunctionalQuivers
    (source-object g)
    (target-object f)
    (comp (.-morphism_function f) (.-morphism_function g))
    (comp (.-object_function f) (.-object_function g))
    (comp (.-out_function f) (.-out_function g))))

; Ontology of morphisms of cofunctional quivers
(defn morphism-of-cofunctional-quivers?
  [obj]

  (= (type obj) MorphismOfCofunctionalQuivers))