(ns locus.elementary.topoi.copresheaf.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.natural-transformation :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)))

; Morphisms in a topos of copresheaves
; Let C be a category and Sets^C its topos of copresheaves. Then a morphism of copresheaves
; is simply a morphism in this topos.
(deftype MorphismOfCopresheaves
  [source-functor target-functor func]

  AbstractMorphism
  (source-object [this] source-functor)
  (target-object [this] target-functor)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Index categories for morphisms of copresheaves
(defmethod index MorphismOfCopresheaves
  [^MorphismOfCopresheaves morphism]

  (category-product t2 (index (source-object morphism))))

; Get sets and function components of morphisms of copresheaves
(defmethod get-set MorphismOfCopresheaves
  [morphism [i v]]

  (case i
    0 (object-apply (source-object morphism) v)
    1 (object-apply (target-object morphism) v)))

(defmethod get-function MorphismOfCopresheaves
  [morphism [[i j] v]]

  (let [source (source-object morphism)
        target (target-object morphism)
        index-category (index source)
        func (.-func morphism)]
    (case [i j]
      [0 0] (morphism-apply source v)
      [1 1] (morphism-apply target v)
      [0 1] (compose
              (morphism-apply target v)
              (func (source-element index-category v))))))

; Composition and identities in the topos of copresheaves
(defmethod identity-morphism Copresheaf
  [copresheaf]

  (MorphismOfCopresheaves.
    copresheaf
    copresheaf
    identity-morphism))

(defmethod compose* MorphismOfCopresheaves
  [a b]

  (MorphismOfCopresheaves.
    (source-object b)
    (target-object a)
    (fn [obj]
      (compose (a obj) (b obj)))))

; Conversion mechanisms for morphisms of copresheaves
(defmethod to-natural-transformation MorphismOfCopresheaves
  [^MorphismOfCopresheaves morphism]

  (->NaturalTransformation
    (to-functor (source-object morphism))
    (to-functor (target-object morphism))
    (.func morphism)))

; Ontology of morphisms of copresheaves
(defn morphism-of-copresheaves?
  [morphism]

  (= (type morphism) MorphismOfCopresheaves))