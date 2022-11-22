(ns locus.order.general.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.skeletal.object :refer :all]
            [locus.order.general.symmetric.object :refer :all])
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

(derive PreorderElement :locus.base.logic.structure.protocols/element)

(defmethod wrap :locus.elementary.copresheaf.core.protocols/thin-category
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
