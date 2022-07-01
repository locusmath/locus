(ns locus.elementary.quiver.dependency.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.permutable.morphism :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all])
  (:import [locus.elementary.quiver.core.object Quiver]
           [locus.elementary.function.core.object SetFunction]
           (locus.elementary.quiver.unital.object UnitalQuiver)
           (locus.elementary.quiver.dependency.object DependencyQuiver)))

; Dependency quivers are simply presheaves over the category consisting of two objects and
; eight morphisms: the source, target, reverse, source identity, target identity, identity
; vertex identity, and edge identity morphisms with their obvious compositions. Then morphisms in
; this topos are the corresponding morphisms of presheaves.

; Generalized morphisms of in the topos of dependency quivers
(defprotocol StructuredMorphismOfDependencyQuivers
  "A structured morphism of dependency quivers is a morphism in a category equipped with a functor
  to te the topos of dependency quivers. An example is a morphism in the category of groupoids."

  (underlying-morphism-of-dependency-quivers [this]
    "Get the underlying morphism of dependency quivers of this morphism."))

; Morphisms in the topos of dependency quivers
(deftype MorphismOfDependencyQuivers [source-quiver target-quiver input-function output-function]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      source-quiver
      target-quiver
      input-function
      output-function))

  StructuredMorphismOfUnitalQuivers
  (underlying-morphism-of-unital-quivers [this] this)

  StructuredMorphismOfPermutableQuivers
  (underlying-morphism-of-permutable-quivers [this] this)

  StructuredMorphismOfDependencyQuivers
  (underlying-morphism-of-dependency-quivers [this] this))

; Composition and morphisms in the topos of dependency quivers
(defmethod compose* MorphismOfDependencyQuivers
  [a b]

  (MorphismOfDependencyQuivers.
    (source-object b)
    (target-object a)
    (compose-functions (first-function a) (first-function b))
    (compose-functions (second-function a) (second-function b))))

(defmethod identity-morphism DependencyQuiver
  [quiv]

  (MorphismOfDependencyQuivers.
    quiv
    quiv
    (identity-function (first-set quiv))
    (identity-function (second-set quiv))))

; Morphisms in the topos of dependency quivers
(defn morphism-of-dependency-quivers?
  [morphism]

  (= (type morphism) MorphismOfDependencyQuivers))