(ns locus.elementary.category.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.monoid.end :refer :all]
            [locus.elementary.group.core.aut :refer :all])
  (:import (locus.elementary.category.core.object Category)))

; Elements of categories
; Let Cat be the concrete category of categories. Then cat consists of structured sets whose objects
; are sections of its underlying Quiver copresheaf: these sections can either be objects or members.
; Its morphisms are functions between elements, which we call functors that preserve certain
; properties of the category. This categorical foundation has two advantages: (1) since it is described
; in terms of the topos Sets, we can use familiar set theoretic machinery to study categories and
; (2) it integrates well with other related topoi like the topos of quivers.

; As sections each of the different elements can be associated with a tag, which describes the
; degree of the element of the category. In this context, objects might be considered to be
; 0-morphisms, morphisms are 1-morphisms, and so on. This extends naturally to 2-morphisms in a
; 2-category and higher morphisms in higher categories as well as infinity-categories. In each
; of the different models of higher category we resort to an underlying topos theoretic foundation
; based upon copresheaves such as simplicial sets and higher quivers.

(deftype CategoryObject [category object]
  Element
  (parent [this] category)

  SectionElement
  (tag [this] 1)
  (member [this] object)

  IdentifiableInstance
  (unwrap [this] (list (tag this) (member this))))

(deftype CategoryMorphism [category morphism]
  Element
  (parent [this] category)

  SectionElement
  (tag [this] 0)
  (member [this] morphism)

  IdentifiableInstance
  (unwrap [this] (list (tag this) (member this)))

  AbstractMorphism
  (source-object [this]
    (CategoryObject. category (source-element category morphism)))
  (target-object [this]
    (CategoryObject. category (target-element category morphism))))

(derive CategoryObject :locus.base.logic.structure.protocols/element)
(derive CategoryMorphism :locus.base.logic.structure.protocols/element)

(defmethod wrap :locus.elementary.copresheaf.core.protocols/category
  [category [i v]]

  (cond
    (= i 0) (CategoryMorphism. category v)
    (= i 1) (CategoryObject. category v)))

; Category elements are joint generalisations of 0-morphisms and 1-morphisms, so in other words they
; essentially refer to n-morphisms regardless of their degree. A category is a structured set consisting
; of n-morphisms between (n-1) morphisms and it can always be described topos theoretically in
; terms of some kind of underlying presheaf.
(defn category-element?
  [element]

  (or
    (= (type element) CategoryObject)
    (= (type element) CategoryMorphism)))

; Category elements
(defn category-objects
  [category]

  (set
    (map
      (fn [object]
        (CategoryObject. category object))
      (objects category))))

(defn category-morphisms
  [category]

  (set
    (map
      (fn [i]
        (CategoryMorphism. category i))
      (first-set category))))

(defn category-elements
  [category]

  (union
    (category-objects category)
    (category-morphisms category)))

; Category objects
(defn category-object?
  [x]

  (= (type x) CategoryObject))

(defn endotrivial-category-object?
  [x]

  (and
    (category-object? x)
    (let [category (.-category ^CategoryObject x)
          obj (.-object ^CategoryObject x)]
      (= 1 (count (quiver-hom-cardinality category obj obj))))))

; Source and target object elements
(defn source-object-element
  [morphism]

  ((.source (.category morphism)) morphism))

(defn target-object-element
  [morphism]

  ((.target (.category morphism)) morphism))

; Composition and identities in arbitrary categories
(defmethod compose* CategoryMorphism
  [a b]

  (->CategoryMorphism
    (.category a)
    ((.func (.category a))
     (list (.morphism a) (.morphism b)))))

(defmethod identity-morphism CategoryObject
  [obj]

  (let [c (.category obj)]
    (CategoryMorphism.
      c
      ((.id ^Category c) (.object obj)))))

; Enumeration of automorphisms and endomorphisms
(defn composable-morphisms?
  [a b]

  (= (target-object b)
     (source-object a)))

(defn morphism?
  [morphism]

  (= (type morphism) CategoryMorphism))

(defn endomorphism?
  [morphism]

  (= (source-object morphism)
     (target-object morphism)))

(defn identity-morphism?
  [morphism]

  (let [category (.category morphism)
        source (source-object morphism)
        target (target-object morphism)]
    (and
      (= source target)
      (= (.morphism morphism) ((.id ^Category category) source)))))

(defn inverses?
  [a b]

  (and
    (= (source-object a) (target-object b))
    (= (target-object a) (source-object b))
    (identity-morphism? (compose a b))
    (identity-morphism? (compose b a))))

(defn isomorphism?
  [morphism]

  (not
    (every?
      (fn [i]
        (not (inverses? morphism i)))
      (category-morphisms (.category morphism)))))

(def automorphism?
  (intersection
    endomorphism?
    isomorphism?))

; We need to be able to get the end monoid and the aut group of an
; object of a category, which can be achieved by morphism enumeration.
(defn enumerate-endomorphisms
  [ob]

  (set
    (filter
      (fn [i]
        (= (source-object-element i)
           (target-object-element i)
           (.object ob)))
      (category-morphisms (.category ob)))))

(defn enumerate-automorphisms
  [ob]

  (set
    (filter
      (fn [i]
        (and
          (isomorphism? i)
          (= (source-object-element i)
             (target-object-element i)
             (.object ob))))
      (category-morphisms (.category ob)))))

(defmethod end CategoryObject
  [obj]

  (->Monoid
    (enumerate-endomorphisms obj)
    (fn [[a b]]
      (compose a b))
    (identity-morphism obj)))

(defmethod aut CategoryObject
  [obj]

  (->Monoid
    (enumerate-automorphisms obj)
    (fn [[a b]]
      (compose a b))
    (identity-morphism obj)))