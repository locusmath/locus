(ns locus.order.join-semilattice.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]))

; A join semilattice is a category having all binary coproducts
(deftype JoinSemilattice [elements join]
  StructuredJoinSemilattice
  (join-fn [this] join)

  ConcreteObject
  (underlying-set [this] elements)

  StructuredDiset
  (first-set [this] (join-precedence-relation elements join))
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

(derive JoinSemilattice :locus.elementary.copresheaf.core.protocols/thin-skeletal-category)

; Underlying relations of join semilattices
(defmethod underlying-relation JoinSemilattice
  [^JoinSemilattice semilattice] (morphisms semilattice))

; Mechanisms for creating join semilattices
(defn relational-join-semilattice
  [rel]

  (JoinSemilattice.
    (vertices rel)
    (join-operation rel)))

; Conversion routines for creating join semilattices
(defmulti to-join-semilattice type)

(defmethod to-join-semilattice JoinSemilattice
  [^JoinSemilattice semilattice] semilattice)

(defmethod to-join-semilattice :locus.base.logic.core.set/universal
  [coll] (relational-join-semilattice coll))

; Products of join semilattices are again join semilattices
(defmethod product JoinSemilattice
  [& join-semilattices]

  (->JoinSemilattice
    (apply cartesian-product (map objects join-semilattices))
    (fn [& colls]
      (map-indexed
        (fn [i semilattice]
          (apply
            (join-fn semilattice)
            (map #(nth % i) colls)))
        join-semilattices))))
