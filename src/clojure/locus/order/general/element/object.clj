(ns locus.order.general.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.skeletal.object :refer :all]
            [locus.order.general.symmetric.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.general.skeletal.object Poset)
           (locus.order.general.symmetric.object Setoid)))

; Elements of preorders, partial orders, setoids, and related structures
; Preorder elements are also instances of objects of thin categories.
(deftype PreorderElement [order elem]
  Element
  (parent [this] order)

  SectionElement
  (tag [this] 1)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this] elem))

(derive PreorderElement :locus.set.logic.structure.protocols/element)

(defmethod wrap :locus.set.copresheaf.structure.core.protocols/thin-category
  [order elem]

  (->PreorderElement order elem))

; Elements of preordered sets
(defn preorder-element?
  [elem] (= (type elem) PreorderElement))

(defn order-element?
  [elem]

  (and
    (preorder-element? elem)
    (= (type (parent elem)) Poset)))

(defn setoid-element?
  [elem]

  (and
    (preorder-element? elem)
    (= (type (parent elem)) Setoid)))

; Additional classes of order elements
(defn minimal-order-element?
  [elem]

  (and
    (order-element? elem)
    (empty? (proper-predecessor-objects (underlying-quiver (parent elem)) (unwrap elem)))))

(defn maximal-order-element?
  [elem]

  (and
    (order-element? elem)
    (empty? (proper-successor-objects (underlying-quiver (parent elem)) (unwrap elem)))))

(defn enclosed-order-element?
  [elem]

  (and
    (order-element? elem)
    (not (minimal-order-element? elem))
    (not (maximal-order-element? elem))))

(def isolated-order-element?
  (intersection
    minimal-order-element?
    maximal-order-element?))
