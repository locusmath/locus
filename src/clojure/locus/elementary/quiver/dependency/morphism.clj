(ns locus.elementary.quiver.dependency.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.permutable.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all])
  (:import [locus.base.function.core.object SetFunction]
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

(derive MorphismOfDependencyQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-dependency-quivers)

; Components of morphisms of permutable quivers
(defmethod get-set MorphismOfDependencyQuivers
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function MorphismOfDependencyQuivers
  [morphism [[i j] v]]

  (let [source-data* [0 1 0 0 1 0 0 0]]
    (case [i j]
      [0 0] (get-function (source-object morphism) v)
      [1 1] (get-function (target-object morphism) v)
      [0 1] (compose
              (get-function (target-object morphism) v)
              (morphism-of-quivers-component-function morphism (get source-data* v))))))

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

; Products and coproducts in the topos of morphisms of quivers
(defmethod product MorphismOfDependencyQuivers
  [& args]

  (->MorphismOfDependencyQuivers
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map first-function args))
    (apply product (map second-function args))))

(defmethod coproduct MorphismOfDependencyQuivers
  [& args]

  (->MorphismOfDependencyQuivers
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map first-function args))
    (apply coproduct (map second-function args))))

; Morphisms in the topos of dependency quivers
(defn morphism-of-dependency-quivers?
  [morphism]

  (= (type morphism) MorphismOfDependencyQuivers))