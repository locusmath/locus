(ns locus.elementary.incidence.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.incidence.core.object :refer :all])
  (:import (locus.elementary.incidence.core.object Span)))

; Elements of span copresheaves
(deftype Edge [span elem]
  Element
  (parent [this] span)

  SectionElement
  (tag [this] 1)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this]
    (list 1 elem)))

(deftype Vertex [span elem]
  Element
  (parent [this] span)

  SectionElement
  (tag [this] 2)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this]
    (list 2 elem)))

(deftype Flag [span elem]
  Element
  (parent [this] span)

  SectionElement
  (tag [this] 0)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this]
    (list 0 elem)))

(derive Flag :locus.base.logic.structure.protocols/element)
(derive Edge :locus.base.logic.structure.protocols/element)
(derive Vertex :locus.base.logic.structure.protocols/element)

(defmethod wrap Span
  [span [i v]]

  (cond
    (= i 0) (Flag. span v)
    (= i 1) (Edge. span v)
    (= i 2) (Vertex. span v)))

; Component vertices and edges of span copresheaf elements
(defn get-vertex
  [^Flag flag]

  (vertex-component (parent flag) (member flag)))

(defn get-edge
  [^Flag flag]

  (edge-component (parent flag) (member flag)))

(defn flag-components
  [^Flag flag]

  (list
    (get-edge flag)
    (get-vertex flag)))

; Ontology of span elements
(defn span-element?
  [elem]

  (or
    (= (type elem) Vertex)
    (= (type elem) Edge)
    (= (type elem) Flag)))

(defn flag?
  [elem]

  (= (type elem) Flag))

(defn vertex?
  [elem]

  (= (type elem) Vertex))

(defn edge?
  [elem]

  (= (type elem) Edge))

