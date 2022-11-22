(ns locus.order.meet-semilattice.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.meet-semilattice.core.object :refer :all])
  (:import (locus.order.meet_semilattice.core.object MeetSemilattice)))

; An object of a thin category having all binary products
(deftype MeetSemilatticeObject
  [lattice elem]

  Element
  (parent [this] lattice)

  SectionElement
  (tag [this] 1)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this] elem))

(derive MeetSemilatticeObject :locus.base.logic.structure.protocols/element)

(defmethod wrap MeetSemilattice
  [^MeetSemilattice source, x]

  (MeetSemilatticeObject. source x))

; Products of objects in meet semilattices
(defmethod product MeetSemilatticeObject
  [& objects]

  (let [current-meet-semilattice (parent (first objects))]
    (MeetSemilatticeObject.
      current-meet-semilattice
      (apply
        (meet-fn current-meet-semilattice)
        (map #(.elem %) objects)))))

; Ontology of meet semilattice elements
(defn meet-semilattice-object?
  [x]

  (= (type x) MeetSemilatticeObject))
