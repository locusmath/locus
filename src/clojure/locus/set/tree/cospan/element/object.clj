(ns locus.set.tree.cospan.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all]
            [locus.set.tree.cospan.core.object :refer :all])
  (:import (locus.set.tree.cospan.core.object Cospan)))

; Elements of cospan copresheaves
(deftype CospanElement [cospan id value]
  Element
  (parent [this] cospan)

  IdentifiableInstance
  (unwrap [this] (list id value))

  SectionElement
  (tag [this] id)
  (member [this] value))

(derive CospanElement :locus.set.logic.structure.protocols/element)

(defmethod wrap Cospan
  [cospan [i v]]

  (CospanElement. cospan i v))

; Get the application of a cospan element along the cospan copresheaf tree
(defn application
  [^CospanElement elem]

  (let [cospan (parent elem)
        id (tag elem)]
    (CospanElement.
      cospan
      id
      (cond
        (= id '(0)) (apply-first-cospan-function cospan (member elem))
        (= id '(1)) (apply-second-cospan-function cospan (member elem))
        (= id '()) (member elem)))))

(defn output-first-fiber
  [^CospanElement elem]

  (let [cospan (parent elem)
        val (member elem)]
    (map
      (fn [i]
        (CospanElement. cospan 0 i))
      (first-fiber cospan val))))

(defn output-second-fiber
  [^CospanElement elem]

  (let [cospan (parent elem)
        val (member elem)]
    (map
      (fn [i]
        (CospanElement. cospan 1 i))
      (second-fiber cospan val))))

(defn output-fiber-pair
  [^CospanElement elem]

  (list (output-first-fiber elem) (output-second-fiber elem)))

; Ontology of cospan elements
(defn cospan-element?
  [x]

  (= (type x) CospanElement))

(defn first-source-element?
  [x]

  (and
    (cospan-element? x)
    (= (tag x) '(0))))

(defn second-source-element?
  [x]

  (and
    (cospan-element? x)
    (= (tag x) '(1))))

(defn output-element?
  [x]

  (and
    (cospan-element? x)
    (= (tag x) '())))

(defn first-missing-output-element?
  [x]

  (and
    (output-element? x)
    (let [val (member x)]
      (empty? (first-fiber cospan val)))))

(defn second-missing-output-element?
  [x]

  (and
    (output-element? x)
    (let [val (member x)]
      (empty? (second-fiber cospan val)))))

(defn completely-missing-output-element?
  [x]

  (and
    (output-element? x)
    (let [val (member x)]
      (empty? (first-fiber cospan val))
      (empty? (second-fiber cospan val)))))