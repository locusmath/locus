(ns locus.elementary.category.comma.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.element.object :refer :all])
  (:import (locus.elementary.category.core.object Category)
           (locus.elementary.category.element.object CategoryMorphism)
           (locus.elementary.diamond.core.object Diamond)
           (locus.base.function.core.object SetFunction)))

; In topos theoretic foundations we start especially with the fundamental topoi: Sets,
; Sets^2, and Sets^(->). The topos Sets^(->) is considered to be an arrow category of
; Sets. We can generalize this process of producing an arrow category from Sets to
; an arbitrary category. We deal with this in this file.

; The morphism of morphisms class
(deftype MorphismOfMorphisms
  [source target in-morphism out-morphism]

  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target))

(defn valid-morphism-of-morphisms?
  [^MorphismOfMorphisms morphism]

  (= (compose (.out_morphism morphism) (source-object morphism))
     (compose (target-object morphism) (.in_morphism morphism))))

(derive MorphismOfMorphisms ::morphism-of-morphisms)

; We can convert morphisms of functions to morphisms of morphisms
(defmulti to-morphism-of-morphisms type)

(defmethod to-morphism-of-morphisms MorphismOfMorphisms
  [morphism] morphism)

(defmethod to-morphism-of-morphisms Diamond
  [morphism]

  (MorphismOfMorphisms.
    (source-object morphism)
    (target-object morphism)
    (input-set-function morphism)
    (output-set-function morphism)))

; Composition and identities in comma categories
(defmethod compose* MorphismOfMorphisms
  [^MorphismOfMorphisms a, ^MorphismOfMorphisms b]

  (MorphismOfMorphisms.
    (source-object b)
    (target-object a)
    (compose (.in_morphism a) (.in_morphism b))
    (compose (.out_morphism a) (.out_morphism b))))

(defn identity-morphism-of-morphisms
  [morphism]

  (MorphismOfMorphisms.
    morphism
    morphism
    (identity-morphism (source-object morphism))
    (identity-morphism (target-object morphism))))

(defmethod identity-morphism CategoryMorphism
  [morphism]

  (identity-morphism-of-morphisms morphism))

; Input actions in a slice category of morphisms from an object X
(deftype InputAction
  [source target in-morphism]

  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target))

(derive InputAction ::morphism-of-morphisms)

(defmethod to-morphism-of-morphisms InputAction
  [^InputAction morphism]

  (MorphismOfMorphisms.
    (source-object morphism)
    (target-object morphism)
    (.in_morphism morphism)
    (identity-morphism (target-object morphism))))

(defmethod compose* InputAction
  [^InputAction a, ^InputAction b]

  (InputAction.
    (source-object b)
    (target-object a)
    (compose (.in_morphism a) (.in_morphism b))))

(defn identity-input-action
  [morphism]

  (InputAction.
    morphism
    morphism
    (identity-morphism (source-object morphism))))

; Output actions in a slice category of morphisms from an object X
(deftype OutputAction
  [source target out-morphism]

  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target))

(derive OutputAction ::morphism-of-morphisms)

(defmethod to-morphism-of-morphisms OutputAction
  [^OutputAction morphism]

  (MorphismOfMorphisms.
    (source-object morphism)
    (target-object morphism)
    (identity-morphism (source-object morphism))
    (.out_morphism morphism)))

(defmethod compose* OutputAction
  [^OutputAction a, ^OutputAction b]

  (InputAction.
    (source-object b)
    (target-object a)
    (compose (.out_morphism a) (.out_morphism b))))

(defn identity-output-action
  [morphism]

  (OutputAction.
    morphism
    morphism
    (identity-morphism (target-object morphism))))

; Ontology of morphisms of morphisms
(defmulti morphism-of-morphisms? type)

(defmethod morphism-of-morphisms? :default
  [x]

  (isa? (type x) ::morphism-of-morphisms))

(defn input-action?
  [morphism]

  (= (type morphism) InputAction))

(defn output-action?
  [morphism]

  (= (type morphism) OutputAction))

; We need special mechanisms to get the
(defn morphism-of-morphisms-of-category?
  [category morphism]

  (let [morphisms (first-set category)
        objects (second-set category)]
    (and
      (= (type morphism) MorphismOfMorphisms)
      (objects (source-object morphism))
      (objects (target-object morphism))
      (morphisms (.in_morphism morphism))
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