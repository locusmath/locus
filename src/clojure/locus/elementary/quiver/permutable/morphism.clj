(ns locus.elementary.quiver.permutable.morphism
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
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all])
  (:import [locus.elementary.quiver.core.object Quiver]
           [locus.base.function.core.object SetFunction]
           (locus.elementary.quiver.permutable.object PermutableQuiver)))

; The topos of permutable quivers is the presheaf topos over the category consisting of two
; objects and five morphisms: the source, the target, the reverse morphism, the edge
; identity and the vertex identity. Then the morphisms in this elementary topos are simply
; the corresponding morphisms of presheaves.

; The structured morphism class will be used to interpret the theory of functors
; from the category of groupoids to the topos of permutable quivers
(defprotocol StructuredMorphismOfPermutableQuivers
  "A structured morphism of permutable quivers is any morphism that has an underlying
   functor to the topos of permutable quivers."

  (underlying-morphism-of-permutable-quivers [this]
    "Get the underlying morphism of permutable quivers of a morphism."))

; Morphisms in the topos of permutable quivers
(deftype MorphismOfPermutableQuivers [source-quiver target-quiver input-function output-function]
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

  StructuredMorphismOfPermutableQuivers
  (underlying-morphism-of-permutable-quivers [this] this))

(derive MorphismOfPermutableQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-permutable-quivers)

; Components of morphisms of permutable quivers
(defmethod get-set MorphismOfPermutableQuivers
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function MorphismOfPermutableQuivers
  [morphism [[i j] v]]

  (let [source-data* [0 1 0 0 0]]
    (case [i j]
      [0 0] (get-function (source-object morphism) v)
      [1 1] (get-function (target-object morphism) v)
      [0 1] (compose
              (get-function (target-object morphism) v)
              (morphism-of-quivers-component-function morphism (get source-data* v))))))

; These types of morphisms are basically distinguished by the fact that they preserve
; the inverse functions of their permutable quivers.
(defn morphism-of-inverse-functions
  [morphism]

  (->Diamond
    (inverse-function (source-object morphism))
    (inverse-function (target-object morphism))
    (underlying-function morphism)
    (underlying-function morphism)))

; Composition and identities in the topos of permutable quivers
(defmethod compose* MorphismOfPermutableQuivers
  [a b]

  (MorphismOfPermutableQuivers.
    (source-object b)
    (target-object a)
    (compose-functions (first-function a) (first-function b))
    (compose-functions (second-function a) (second-function b))))

(defmethod identity-morphism PermutableQuiver
  [quiv]

  (MorphismOfPermutableQuivers.
    quiv
    quiv
    (identity-function (first-set quiv))
    (identity-function (second-set quiv))))

; Products and coproducts in the topos of morphisms of quivers
(defmethod product MorphismOfPermutableQuivers
  [& args]

  (->MorphismOfPermutableQuivers
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map first-function args))
    (apply product (map second-function args))))

(defmethod coproduct MorphismOfPermutableQuivers
  [& args]

  (->MorphismOfPermutableQuivers
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map first-function args))
    (apply coproduct (map second-function args))))

; Ontology of morphisms in the topos of permutable quivers
(defn morphism-of-permutable-quivers?
  [morphism]

  (= (type morphism) MorphismOfPermutableQuivers))


