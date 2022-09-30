(ns locus.elementary.bijection.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.bijection.core.object Bijection)))

; Input and output elements of bijections
(deftype BijectionInput [func in]
  Element
  (parent [this] func)

  SectionElement
  (tag [this] 0)
  (member [this] in)

  IdentifiableInstance
  (unwrap [this]
    (list 0 in)))

(deftype BijectionOutput [func out]
  Element
  (parent [this] func)

  SectionElement
  (tag [this] 1)
  (member [this] out)

  IdentifiableInstance
  (unwrap [this]
    (list 1 out)))

(derive BijectionInput :locus.base.logic.structure.protocols/element)
(derive BijectionOutput :locus.base.logic.structure.protocols/element)

(defmethod wrap Bijection
  [func [i v]]

  (if (zero? i)
    (BijectionInput. func v)
    (BijectionOutput. func v)))

; Application and inverse application of bijection elements
(defn application
  [^BijectionInput input]

  (let [func (parent input)
        val (member input)
        new-val (func val)]
    (BijectionOutput. func new-val)))

(defn unapplication
  [^BijectionOutput output]

  (let [func (parent output)
        val (member output)
        new-val ((inv func) val)]
    (BijectionInput. func new-val)))

; Ontology of bijection elements
(defn bijection-element?
  [elem]

  (or
    (= (type elem) BijectionInput)
    (= (type elem) BijectionOutput)))

(defn bijection-input?
  [elem]

  (= (type elem) BijectionInput))

(defn bijection-output?
  [elem]

  (= (type elem) BijectionOutput))
