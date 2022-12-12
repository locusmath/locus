(ns locus.order.meet-semilattice.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; A meet semilattice is a category having all binary products
(deftype MeetSemilattice [elements meet]
  StructuredMeetSemilattice
  (meet-fn [this] meet)
  
  ConcreteObject
  (underlying-set [this] elements)

  StructuredDiset
  (first-set [this] (meet-precedence-relation elements join-multisets))
  (second-set [this] elements)

  StructuredQuiver
  (underlying-quiver [this] (relational-quiver (objects this) (morphisms this)))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (relational-unital-quiver (objects this) (morphisms this)))
  (identity-morphism-of [this x] (list x x))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (first-set this))

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive MeetSemilattice :locus.set.copresheaf.structure.core.protocols/thin-skeletal-category)

; Underlying relations of meet semilattices
(defmethod underlying-relation MeetSemilattice
  [^MeetSemilattice semilattice] (morphisms semilattice))

; Create a meet semilattice from a set of ordered pairs
(defn relational-meet-semilattice
  [rel]

  (MeetSemilattice.
    (vertices rel)
    (meet-operation rel)))

; Conversion routines for creating meet semilattices
(defmulti to-meet-semilattice type)

(defmethod to-meet-semilattice MeetSemilattice
  [^MeetSemilattice semilattice] semilattice)

(defmethod to-meet-semilattice :locus.set.logic.core.set/universal
  [coll] (relational-meet-semilattice coll))

; Products of join semilattices are again join semilattices
(defmethod product MeetSemilattice
  [& meet-semilattices]

  (->MeetSemilattice
    (apply cartesian-product (map objects meet-semilattices))
    (fn [& colls]
      (map-indexed
        (fn [i semilattice]
          (apply
            (meet-fn semilattice)
            (map #(nth % i) colls)))
        meet-semilattices))))