(ns locus.set.copresheaf.incidence.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.copresheaf.bijection.core.object :refer :all]
            [locus.set.copresheaf.incidence.core.object :refer :all])
  (:import (locus.set.copresheaf.incidence.core.object Span)))

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

(derive Flag :locus.set.logic.structure.protocols/element)
(derive Edge :locus.set.logic.structure.protocols/element)
(derive Vertex :locus.set.logic.structure.protocols/element)

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

