(ns locus.elementary.category.comma.category
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.morphism.category-morphism :refer :all]
            [locus.elementary.category.comma.morphism :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import (locus.elementary.category.core.object Category)
           (locus.elementary.category.morphism.category_morphism CategoryMorphism)
           (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.function.core.object SetFunction)))

; Let C be a category, then C^(->) is its arrow category. This category has special morphisms that define it
; which are provided separately in the morphism file. These morphisms are defined by the MorphismOfMorphisms
; class. Arrow categories are uniquely associated with special subcategories called comma categories for each
; object which are the under and over categories respectively. So as special cases, in order to construct
; the under and over categories we have input action and output action classes.

; Arrow categories play a fundamental role in topos theory by their relationship with the elementary topos
; Sets^(->). In addition, topoi are distinguished by the fact that their over categories are again topoi.
; As a consequence, we play special attention here to the construction of under and over categories
; from a category and one of its objects.

; Construction of arrow categories
(defn arrow-category
  [category]

  (Category.
    (->Universal
      (partial morphism-of-morphisms-of-category? category))
    (morphisms category)
    source-object
    target-object
    (fn [[a b]]
      (compose a b))
    identity-morphism-of-morphisms))

(defn input-action-category
  [category]

  (Category.
    (->Universal
      (partial input-action-of-category? category))
    (morphisms category)
    source-object
    target-object
    (fn [[a b]]
      (compose a b))
    identity-input-action))

(defn output-action-category
  [category]

  (Category.
    (->Universal
      (partial output-action-of-category? category))
    (morphisms category)
    source-object
    target-object
    (fn [[a b]]
      (compose a b))
    identity-output-action))

; Constructions of comma categories
(defn over-category
  [category x]

  (Category.
    (->Universal
      (partial morphism-of-over-category? category x))
    (over-morphisms category x)
    source-object
    target-object
    (fn [[a b]]
      (compose a b))
    identity-input-action))

(defn under-category
  [category x]

  (Category.
    (->Universal
      (partial morphism-of-under-category? category x))
    (under-morphisms category x)
    source-object
    target-object
    (fn [[a b]]
      (compose a b))
    identity-output-action))

