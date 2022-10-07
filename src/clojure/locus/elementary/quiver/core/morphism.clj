(ns locus.elementary.quiver.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import [locus.elementary.quiver.core.object Quiver]
           [locus.base.function.core.object SetFunction]))

; A morphism in the topos of quivers is a natural transformation of the underlying
; copresheaves of the two quivers. It follows that there are Sets^(->) valued functors
; that define commutative diagrams over the source and target functions of the quiver,
; with respect to any morphism in the topos of quivers. Furthermore, there is a subobject
; classifier of Quivers, which we implement in this file.

; A protocol that abstracts the idea of a morphism of quivers
(defprotocol StructuredMorphismOfQuivers
  "Let f : C -> Quiv define a category C structured over the topos of quivers. Then every morphism in
  C is associated to a morphism of quivers. This protocol defines the morphism part of functorial mappings
  of this sort, which are frequently encountered in category theory and topos theory."

  (underlying-morphism-of-quivers [this]
    "This takes a morphism and returns its corresponding morphism in the topos of quivers."))

; Morphism of quivers
(deftype MorphismOfQuivers [source-quiver target-quiver input-function output-function]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  ConcreteMorphism
  (inputs [this] (underlying-set (source-object this)))
  (outputs [this] (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [(inputs this) (outputs this)]))

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this] this)

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i 0) (list 0 (input-function v))
      (= i 1) (list 1 (output-function v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive MorphismOfQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-quivers)

; Composition and identities in the topos of quivers
(defmethod compose* MorphismOfQuivers
  [a b]

  (MorphismOfQuivers.
   (source-object b)
   (target-object a)
   (compose-functions (first-function a) (first-function b))
   (compose-functions (second-function a) (second-function b))))

(defmethod identity-morphism Quiver
  [quiv]

  (MorphismOfQuivers.
    quiv
    quiv
    (identity-function (first-set quiv))
    (identity-function (second-set quiv))))

; The component functions of a morphism of quivers
(defn morphism-component-function
  [morphism]

  (->SetFunction
    (morphisms (source-object morphism))
    (morphisms (target-object morphism))
    (first-function morphism)))

(defn object-component-function
  [morphism]

  (->SetFunction
    (objects (source-object morphism))
    (objects (target-object morphism))
    (second-function morphism)))

; We can get for any quiver morphism a function morphism for its source and target
; components. In general, topoi of set valued functors can be reduced by any
; given subcategory of their index category.
(defn morphism-of-source-functions
  [morphism]

  (->Diamond
    (source-function (source-object morphism))
    (source-function (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

(defn morphism-of-target-functions
  [morphism]

  (->Diamond
    (target-function (source-object morphism))
    (target-function (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

; We need to be able to get image quivers
(defn image-quiver
  [func]

  (subquiver
    (underlying-quiver (target-object func))
    (function-image (first-function func))
    (function-image (second-function func))))

(defn kernel-quotient
  [func]

  (quotient-quiver
    (underlying-quiver (source-object func))
    (function-kernel (first-function func))
    (function-kernel (second-function func))))

; Subobject classifier in the topos of quivers
(def truth-quiver
  (Quiver.
   '#{#{} #{s} #{t} #{s t} #{s t e}}
   #{0 1}
   '{#{} 0
     #{s} 0
     #{t} 1
     #{s t} 1
     #{s t e} 1}
   '{#{} 0
     #{s} 1
     #{t} 0
     #{s t} 1
     #{s t e} 1}))

(defn classify-quiver-truth
  [quiver new-edges new-vertices elem]

  (union
   (if (contains? new-edges elem) '#{e} #{})
   (if (contains? new-vertices (source-element quiver elem)) '#{s} #{})
   (if (contains? new-vertices (target-element quiver elem)) '#{t} #{})))

(defn subquiver-character
  [quiver new-edges new-vertices]

  (MorphismOfQuivers.
   quiver
   truth-quiver
   (SetFunction.
    (.edges quiver)
    '#{#{} #{s} #{t} #{s t} #{s t e}}
    (fn [e]
      (classify-quiver-truth quiver new-edges new-vertices e)))
   (SetFunction.
    (.vertices quiver)
    #{0 1}
    (fn [v]
      (if (contains? new-vertices v) 1 0)))))

; Products and coproducts in the topos of morphisms of quivers
(defmethod product MorphismOfQuivers
  [& args]

  (->MorphismOfQuivers
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map morphism-component-function args))
    (apply product (map object-component-function args))))

(defmethod coproduct MorphismOfQuivers
  [& args]

  (->MorphismOfQuivers
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map morphism-component-function args))
    (apply coproduct (map object-component-function args))))

; Classification of morphisms of quivers
(defn morphism-of-quivers?
  [m]

  (= (type m) MorphismOfQuivers))
