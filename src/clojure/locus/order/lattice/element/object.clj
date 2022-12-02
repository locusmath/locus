(ns locus.order.lattice.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.order.lattice.core.object Lattice)))

; Let L be a lattice. Then L is a thin category containing all binary products
; and coproducts. The objects of this category C are elements of the lattice L.
; This file defines a class of lattice objects that implements and overrides
; the product and coproduct operations for lattice objects, so that they
; correspond appropriately to meets and joins.
(deftype LatticeObject
  [lattice elem]

  Element
  (parent [this]
    lattice)

  SectionElement
  (tag [this] 1)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this]
    elem))

(derive LatticeObject :locus.base.logic.structure.protocols/element)

(defmethod wrap Lattice
  [lattice elem]

  (LatticeObject. lattice elem))

; Methods dealing with objects of lattice categories
(defn lattice-objects
  [lattice]

  (set
    (map
      (fn [i]
        (LatticeObject.
          lattice
          i))
      (underlying-set lattice))))

(defmethod coproduct LatticeObject
  [& objects]

  (let [current-lattice (parent (first objects))]
    (LatticeObject.
      current-lattice
      (apply
        (join-fn current-lattice)
        (map #(.elem %) objects)))))

(defmethod product LatticeObject
  [& objects]

  (let [current-lattice (parent (first objects))]
    (LatticeObject.
      current-lattice
      (apply
        (meet-fn current-lattice)
        (map #(.elem %) objects)))))

; Ontology of lattice elements
(defn lattice-element?
  [elem]

  (= (type elem) Lattice))