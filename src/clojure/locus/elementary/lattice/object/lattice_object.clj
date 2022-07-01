(ns locus.elementary.lattice.object.lattice-object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]))

; Let L be a lattice. Then L is a thin category containing all binary products
; and coproducts. The objects of this category C are elements of the lattice L.
; This file defines a class of lattice objects that implements and overrides
; the product and coproduct operations for lattice objects, so that they
; correspond appropriately to meets and joins.

(deftype LatticeObject
  [lattice elem])

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

  (let [current-lattice (.lattice (first objects))]
    (LatticeObject.
      current-lattice
      (apply
        (join-fn current-lattice)
       (map #(.elem %) objects)))))

(defmethod product LatticeObject
  [& objects]

  (let [current-lattice (.lattice (first objects))]
    (LatticeObject.
     current-lattice
     (apply
       (meet-fn current-lattice)
       (map #(.elem %) objects)))))
