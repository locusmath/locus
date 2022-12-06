(ns locus.algebra.category.arrow.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.algebra.category.element.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.natural.transformation :refer :all]
            [locus.algebra.category.concrete.categories :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.algebra.category.core.object Category)
           (locus.algebra.category.element.object CategoryMorphism)
           (locus.quiver.unary.core.morphism Diamond)
           (locus.base.function.core.object SetFunction)))

; Let C be a category. Then its arrow category Arr(C), can be formed by defining the
; functor category [T_2,C] in the category of categories. The slice categories
; can then be defined by the subcategories of this arrow category. This generalizes
; the fundamental construction of the topos Sets^{->}.

(deftype ArrowTransformation [category source target in-morphism out-morphism]
  AbstractMorphism
  (source-object [this]
    (arrow-functor category source))
  (target-object [this]
    (arrow-functor category target))

  clojure.lang.IFn
  (invoke [n]
    (case n
      0 in-morphism
      1 out-morphism))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ::arrow-transformation :locus.algebra.category.natural.transformation/natural-transformation)

; The index categories of categorical diamonds are weak orders of the form [1,2,1]
(defmethod index ::arrow-transformation
  [transformation]

  (let [ordered-pair-category (thin-category '#{(0 0) (0 1) (1 1)})]
    (category-product ordered-pair-category ordered-pair-category)))

; Conversion routines for natural transformations of arrow functors
(defmethod to-natural-transformation ::arrow-transformation
  [transformation]

  (->NaturalTransformation
    (source-object transformation)
    (target-object transformation)
    (fn [x]
      (transformation x))))

(defmethod to-functor ::arrow-transformation
  [transformation]

  (to-functor (to-natural-transformation transformation)))

; Convert various objects into arrow transformations
(defmulti to-arrow-transformation type)

(defmethod to-arrow-transformation ArrowTransformation
  [transformation] transformation)

(defmethod to-arrow-transformation Diamond
  [diamond]

  (ArrowTransformation.
    sets
    (source-object diamond)
    (target-object diamond)
    (first-function diamond)
    (second-function diamond)))

; Composition of natural transformations of arrow functors is closed
(defmethod compose* ArrowTransformation
  [^ArrowTransformation a, ^ArrowTransformation b]

  (ArrowTransformation.
    (.-category a)
    (source-object b)
    (target-object a)
    (compose (.-in_morphism a) (.-in_morphism b))
    (compose (.-out_morphism a) (.-out_morphism b))))

(defn identity-arrow-transformation
  [category morphism]

  (->ArrowTransformation
    category
    morphism
    morphism
    (identity-morphism-of category morphism)
    (identity-morphism-of category morphism)))

; Input actions in a slice category of morphisms from an object X
(deftype InputAction
  [category source target in-morphism]

  AbstractMorphism
  (source-object [this]
    (arrow-functor category source))
  (target-object [this]
    (arrow-functor category target))

  clojure.lang.IFn
  (invoke [this arg]
    (case arg
      0 in-morphism
      1 (identity-morphism-of category target)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive InputAction ::arrow-transformation)

(defmethod to-arrow-transformation InputAction
  [^InputAction action]

  (->ArrowTransformation
    (.-category action)
    (.-source action)
    (.-target action)
    (action 0)
    (action 1)))

(defmethod compose* InputAction
  [^InputAction a, ^InputAction b]

  (InputAction.
    (.-category a)
    (source-object b)
    (target-object a)
    (compose (.-in_morphism a) (.-in_morphism b))))

(defn identity-input-action
  [category arrow]

  (InputAction.
    category
    arrow
    arrow
    (identity-morphism-of category arrow)))

; Output actions in a slice category of morphisms from an object X
(deftype OutputAction
  [category source target out-morphism]

  AbstractMorphism
  (source-object [this]
    (arrow-functor category source))
  (target-object [this]
    (arrow-functor category target))

  clojure.lang.IFn
  (invoke [this arg]
    (case arg
      0 (identity-morphism-of category source)
      1 out-morphism))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive OutputAction ::arrow-transformation)

(defmethod to-arrow-transformation OutputAction
  [^OutputAction action]

  (->ArrowTransformation
    (.-category action)
    (.-source action)
    (.-target action)
    (action 0)
    (action 1)))

(defmethod compose* OutputAction
  [^OutputAction a, ^OutputAction b]

  (InputAction.
    (.-category a)
    (source-object b)
    (target-object a)
    (compose (.-out_morphism a) (.-out_morphism b))))

(defn identity-output-action
  [category arrow]

  (OutputAction.
    category
    arrow
    arrow
    (identity-morphism-of category arrow)))

; Validity check for natural transformations
(defn valid-arrow-transformation?
  [^ArrowTransformation morphism]

  (= (compose (.out_morphism morphism) (source-object morphism))
     (compose (target-object morphism) (.in_morphism morphism))))

; Ontology of categorical diamonds
(defmulti arrow-transformation? type)

(defmethod arrow-transformation? ::arrow-transformation
  [transformation] true)

(defn input-action?
  [morphism]

  (= (type morphism) InputAction))

(defn output-action?
  [morphism]

  (= (type morphism) OutputAction))

; We need special mechanisms to get the
(defn morphism-of-arrow-category?
  [category morphism]

  (let [morphisms (first-set category)
        objects (second-set category)]
    (and
      (= (type morphism) ArrowTransformation)
      (objects (source-object morphism))
      (objects (target-object morphism))
      (morphisms (.in_morphism morphism))
      (morphisms (.out_morphism morphism)))))

(defn input-action-of-category?
  [category morphism]

  (let [morphisms (first-set category)
        objects (second-set category)]
    (and
      (= (type morphism) InputAction)
      (objects (source-object morphism))
      (objects (target-object morphism))
      (morphisms (.in_morphism morphism)))))

(defn output-action-of-category?
  [category morphism]

  (let [morphisms (first-set category)
        objects (second-set category)]
    (and
      (= (type morphism) OutputAction)
      (objects (source-object morphism))
      (objects (target-object morphism))
      (morphisms (.out_morphism morphism)))))

(defn morphism-of-over-category?
  [category out-object morphism]

  (let [morphisms (first-set category)
        objects (second-set category)]
    (and
      (= (type morphism) InputAction)
      (= (target-object morphism) out-object)
      (objects (source-object category))
      (morphisms (.in_morphism category)))))

(defn morphism-of-under-category?
  [category in-object morphism]

  (let [morphisms (first-set category)
        objects (second-set category)]
    (and
      (= (type morphism) OutputAction)
      (= (source-object morphism) in-object)
      (objects (target-object morphism))
      (morphisms (.out_morphism category)))))



