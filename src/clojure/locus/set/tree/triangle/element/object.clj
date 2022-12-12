(ns locus.set.tree.triangle.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.tree.triangle.core.object :refer :all])
  (:import (locus.set.tree.triangle.core.object SetTriangle)))

; Elements of triangle copresheaves
(deftype TriangleElement [triangle id value]
  Element
  (parent [this] triangle)

  IdentifiableInstance
  (unwrap [this] (list id value))

  SectionElement
  (tag [this] id)
  (member [this] value))

(derive TriangleElement :locus.set.logic.structure.protocols/element)

(defmethod wrap SetTriangle
  [^SetTriangle triangle [i v]]

  (TriangleElement. triangle i v))

; Application of elements of the triangle copresheaf
(defn application
  [^TriangleElement elem]

  (let [triangle (parent elem)
        id (tag elem)
        val (member elem)
        new-id (inc id)
        new-val (case id
                  '(0 0) ((prefunction triangle) val)
                  '(0) ((postfunction triangle) val)
                  '() val)]
    (->TriangleElement triangle new-id new-val)))

; Ontology of triangle elements
(defn triangle-element?
  [element]

  (= (type element) TriangleElement))

(defn source-triangle-element?
  [^TriangleElement element]

  (and
    (triangle-element? element)
    (= (tag element) 0)))

(defn middle-triangle-element?
  [^TriangleElement element]

  (and
    (triangle-element? element)
    (= (tag element) 1)))

(defn target-triangle-element?
  [^TriangleElement element]

  (and
    (triangle-element? element)
    (= (tag element) 2)))