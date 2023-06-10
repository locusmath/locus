(ns locus.set.copresheaf.topoi.representable.copresheaf
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.core.contravariant-functor :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]))

; A copresheaf Hom(a,-)
(deftype RepresentableCopresheaf [category object]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] sets)

  StructuredDifunction
  (first-function [this]
    (fn [morphism]
      (let [[x y] (transition category morphism)]
        (->SetFunction
          (quiver-hom-class category object x)
          (quiver-hom-class category object y)
          (fn [arrow]
            (category (list arrow morphism)))))))
  (second-function [this]
    (fn [x]
      (quiver-hom-class category object x))))

; Get the sets and objects of representable copresheaves
(defmethod get-set RepresentableCopresheaf
  [presheaf x]

  ((second-function presheaf) x))

(defmethod get-function RepresentableCopresheaf
  [presheaf x]

  ((first-function presheaf) x))

; The index categories of representable copresheaves
(defmethod index RepresentableCopresheaf
  [presheaf] (source-object presheaf))

; Convert these representable copresheaves into functors
(defmethod to-functor RepresentableCopresheaf
  [copresheaf]

  (->Functor
    (source-object copresheaf)
    (target-object copresheaf)
    (partial get-set copresheaf)
    (partial get-function copresheaf)))

; A natural transformation of Hom(a,-) functors
(deftype MorphismOfRepresentableCopresheaves [category morphism]
  AbstractMorphism
  (source-object [this] (RepresentableCopresheaf. category (source-element category morphism)))
  (target-object [this] (RepresentableCopresheaf. category (target-element category morphism)))

  clojure.lang.IFn
  (invoke [this x]
    (let [[a b] (transition category morphism)]
      (->SetFunction
        (quiver-hom-class category b x)
        (quiver-hom-class category a x)
        (fn [argument-arrow]
          (category (list argument-arrow morphism))))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defmethod identity-morphism RepresentableCopresheaf
  [^RepresentableCopresheaf copresheaf]

  (let [category (.-category copresheaf)
        obj (.-object copresheaf)]
    (MorphismOfRepresentableCopresheaves. category (identity-morphism-of category obj))))

(defmethod compose* MorphismOfRepresentableCopresheaves
  [^MorphismOfRepresentableCopresheaves a, ^MorphismOfRepresentableCopresheaves b]

  (let [category (.-category b)
        f (.-morphism a)
        g (.-morphism b)]
    (MorphismOfRepresentableCopresheaves
      category
      (category (list g f)))))