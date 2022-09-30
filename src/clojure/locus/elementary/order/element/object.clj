(ns locus.elementary.order.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.order.core.object :refer :all])
  (:import (locus.elementary.order.core.object Poset)))

; Elements of partially ordered sets
(deftype OrderElement [order elem]
  Element
  (parent [this] order)

  SectionElement
  (tag [this] 1)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this] elem))

(derive OrderElement :locus.base.logic.structure.protocols/element)

(defmethod wrap Poset
  [order elem]

  (->OrderElement order elem))

; Elements of partially ordered sets
(defn order-element?
  [elem]

  (= (type elem) OrderElement))
