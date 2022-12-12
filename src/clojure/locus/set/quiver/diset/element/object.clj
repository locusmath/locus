(ns locus.set.quiver.diset.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.diset.core.object :refer :all])
  (:import (locus.set.quiver.diset.core.object Diset)))

; Elements of diset copresheaves
(deftype DisetElement [diset id value]
  Element
  (parent [this] diset)

  IdentifiableInstance
  (unwrap [this] (list id value))

  SectionElement
  (tag [this] id)
  (member [this] value))

(derive DisetElement :locus.set.logic.structure.protocols/element)

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