(ns locus.quiver.diset.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.diset.core.object :refer :all])
  (:import (locus.quiver.diset.core.object Diset)))

; Elements of diset copresheaves
(deftype DisetElement [diset id value]
  Element
  (parent [this] diset)

  IdentifiableInstance
  (unwrap [this] (list id value))

  SectionElement
  (tag [this] id)
  (member [this] value))

(derive DisetElement :locus.base.logic.structure.protocols/element)

(defmethod wrap Diset
  [diset [i v]]

  (->DisetElement diset i v))

; Ontology of diset elements
(defn diset-element?
  [obj]

  (= (type obj) DisetElement))

(defn first-member?
  [obj]

  (and
    (diset-element? obj)
    (zero? (tag obj))))

(defn second-member?
  [obj]

  (and
    (diset-element? obj)
    (= (tag obj) 1)))