(ns locus.order.lattice.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
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

(derive LatticeObject :locus.set.logic.structure.protocols/element)

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