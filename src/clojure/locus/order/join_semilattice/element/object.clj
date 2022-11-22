(ns locus.order.join-semilattice.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.join-semilattice.core.object :refer :all])
  (:import (locus.order.join_semilattice.core.object JoinSemilattice)))

; An object of a thin category having all binary coproducts
(deftype JoinSemilatticeObject
  [lattice elem]

  Element
  (parent [this] lattice)

  SectionElement
  (tag [this] 1)
  (member [this] elem)

  IdentifiableInstance
  (unwrap [this] elem))

(derive JoinSemilatticeObject :locus.base.logic.structure.protocols/element)

(defmethod wrap JoinSemilattice
  [^JoinSemilattice source, x]

  (JoinSemilatticeObject. source x))

; Coproducts of objects in join semilattices
(defmethod coproduct JoinSemilatticeObject
  [& objects]

  (let [current-join-semilattice (parent (first objects))]
    (JoinSemilatticeObject.
      current-join-semilattice
      (apply
        (join-fn current-join-semilattice)
        (map #(.elem %) objects)))))

; Ontology of join semilattice elements
(defn join-semilattice-element?
  [x]

  (= (type x) JoinSemilatticeObject))