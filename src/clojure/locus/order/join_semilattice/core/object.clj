(ns locus.order.join-semilattice.core.object
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

(derive JoinSemilattice :locus.set.copresheaf.structure.core.protocols/thin-skeletal-category)

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

(defmethod to-join-semilattice :locus.set.logic.core.set/universal
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
