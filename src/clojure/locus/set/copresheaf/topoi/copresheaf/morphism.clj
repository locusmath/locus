(ns locus.set.copresheaf.topoi.copresheaf.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.natural.transformation :refer :all]
            [locus.set.action.global.object :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.set.quiver.diset.core.morphism :refer :all])
  (:import (locus.set.copresheaf.topoi.copresheaf.object Copresheaf)
           (locus.set.quiver.diset.core.morphism Difunction)
           (locus.set.quiver.unary.core.morphism Diamond)))

; Morphisms in a topos of copresheaves
; Let C be a category and Sets^C its topos of copresheaves. Then a morphism of copresheaves is a
; morphism in the topos Sets^C. By a simple construction, we can also treat this as a copresheaf
; object of a topos in its own right by using the topos Sets^{T_2 x C}. We will use this
; in order to create the presheaf theoretic logic of morphisms of presheaves. This is an important
; part of making presheaf topos theory a holistic system, in which it is possible not only
; to reason about presheaves but morphisms of them as well. With this, presheaf topos theory
; is a complete system of reasoning.
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

; Index categories for morphisms of copresheaves treated as copresheaves
(defmethod index MorphismOfCopresheaves
  [^MorphismOfCopresheaves morphism]

  (category-product t2 (index (source-object morphism))))

; Get the component function of a morphism of copresheaves by a I-object
(defn morphism-of-copresheaves-component-function
  [morphism x]

  (morphism x))

; Get the component diamond of a morphism of copresheaves by an I-morphism
(defn morphism-of-copresheaves-component-diamond
  [morphism x]

  (let [cat (index (source-object morphism))
        source (source-element cat x)
        target (target-element cat x)]
    (->Diamond
     (get-function (source-object morphism) x)
     (get-function (target-object morphism) x)
     (morphism source)
     (morphism target))))

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

; Conversion routines for morphisms of copresheaves
(defmulti to-morphism-of-copresheaves type)

(defmethod to-morphism-of-copresheaves MorphismOfCopresheaves
  [morphism] morphism)

(defmethod to-morphism-of-copresheaves :locus.set.logic.structure.protocols/set-function
  [func]

  (->MorphismOfCopresheaves
    (to-copresheaf (source-object func))
    (to-copresheaf (target-object func))
    (constantly func)))

(defmethod to-morphism-of-copresheaves :locus.set.copresheaf.structure.core.protocols/bijection
  [bijection] (to-morphism-of-copresheaves (underlying-function bijection)))

(defmethod to-morphism-of-copresheaves Diamond
  [diamond]

  (->MorphismOfCopresheaves
    (to-copresheaf (source-object diamond))
    (to-copresheaf (target-object diamond))
    (fn [i]
      (case i
        0 (first-function diamond)
        1 (second-function diamond)))))

; Conversion mechanisms for morphisms of copresheaves
(defmethod to-natural-transformation MorphismOfCopresheaves
  [^MorphismOfCopresheaves morphism]

  (->NaturalTransformation
    (to-functor (source-object morphism))
    (to-functor (target-object morphism))
    (.func morphism)))

; Get the section function of a morphism of copresheaves
(defn section-function
  [func]

  (->SetFunction
    (sections (source-object func))
    (sections (target-object func))
    (fn [[tag elem]]
      (list tag ((func tag) elem)))))

; Create a morphism of constant copresheaves by a diagonal functor
(defn morphism-of-constant-copresheaves
  [category function]

  (->MorphismOfCopresheaves
    (constant-copresheaf category (inputs function))
    (constant-copresheaf category (outputs function))
    (constantly function)))

; Apply the index sum on the level of morphisms of copresheaves
(defn morphism-index-sum
  [& morphisms]

  (->MorphismOfCopresheaves
    (apply index-sum (map source-object morphisms))
    (apply index-sum (map target-object morphisms))
    (fn [i obj]
      (list i ((nth morphisms i) obj)))))
