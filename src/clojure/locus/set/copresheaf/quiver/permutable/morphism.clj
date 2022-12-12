(ns locus.set.copresheaf.quiver.permutable.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import [locus.set.quiver.binary.core.object Quiver]
           [locus.set.mapping.general.core.object SetFunction]
           (locus.set.copresheaf.quiver.permutable.object PermutableQuiver)))

; The topos of permutable quivers is the presheaf topos over the category consisting of two
; objects and five morphisms: the source, the target, the reverse morphism, the edge
; identity and the vertex identity. Then the morphisms in this elementary topos are simply
; the corresponding morphisms of presheaves.

; Morphisms in the topos of permutable quivers
(deftype MorphismOfPermutableQuivers [source-quiver target-quiver input-function output-function]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function))

(derive MorphismOfPermutableQuivers :locus.set.copresheaf.structure.core.protocols/morphism-of-structured-permutable-quivers)

; A structured morphism of permutable quivers is any morphism that is a member of a category
; that comes equipped with a forgetful functor to the topos of permutable quivers. The
; underlying-morphism-of-permutable-quivers method gets this underlying morphism
; of permutable quivers.
(defmulti underlying-morphism-of-permutable-quivers type)

(defmethod underlying-morphism-of-permutable-quivers MorphismOfPermutableQuivers
  [^MorphismOfPermutableQuivers morphism] morphism)

(defmethod underlying-morphism-of-permutable-quivers :default
  [morphism]

  (->MorphismOfPermutableQuivers
    (underlying-permutable-quiver (source-object morphism))
    (underlying-permutable-quiver (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

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


