(ns locus.algebra.category.arrow.category
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.category.element.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.algebra.category.arrow.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.algebra.category.core.object Category)
           (locus.algebra.category.element.object CategoryMorphism)
           (locus.quiver.unary.core.morphism Diamond)
           (locus.base.function.core.object SetFunction)))

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
    (->UnitalQuiver
      (partial arrow-transformation? category)
      (morphisms category)
      source-object
      target-object
      identity-arrow-transformation)
    (fn [[a b]]
      (compose a b))))

(defn input-action-category
  [category]

  (Category.
    (->UnitalQuiver
      (partial input-action-of-category? category)
      (morphisms category)
      source-object
      target-object
      identity-input-action)
    (fn [[a b]]
      (compose a b))))

(defn output-action-category
  [category]

  (Category.
    (->UnitalQuiver
      (partial output-action-of-category? category)
      (morphisms category)
      source-object
      target-object
      identity-output-action)
    (fn [[a b]]
      (compose a b))))

; Construction of comma categories
(defn over-category
  [category x]

  (Category.
    (->UnitalQuiver
      (partial morphism-of-over-category? category x)
      (over-morphisms category x)
      source-object
      target-object
      identity-input-action)
    (fn [[a b]]
      (compose a b))))

(defn under-category
  [category x]

  (Category.
    (->UnitalQuiver
      (partial morphism-of-under-category? category x)
      (under-morphisms category x)
      source-object
      target-object
      identity-output-action)
    (fn [[a b]]
      (compose a b))))


