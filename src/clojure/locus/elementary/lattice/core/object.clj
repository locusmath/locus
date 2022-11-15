(ns locus.elementary.lattice.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.base.logic.core.set Multiset)
           (locus.elementary.relation.binary.sr SeqableRelation)
           (locus.elementary.quiver.core.object Quiver)))

; A lattice is a thin category C containing all binary products and coproducts.
; The coproducts are joins and the products are meets.

; A number of data types represent lattices, including heyting algebras and total orders.
(defprotocol StructuredLattice
  "A general protocol for treating various types of structures as lattices."

  (join-fn [this]
    "the variadic join function of this lattice")
  (meet-fn [this]
    "the variadic meet function of this lattice"))

; Precedence relations for join and meet operations
(defn join-precedence-relation
  [coll join]

  (SeqableRelation.
    coll
    (fn [[a b]]
      (= (join a b) b))
    {}))

(defn meet-precedence-relation
  [coll meet]

  (SeqableRelation.
    coll
    (fn [[a b]]
      (= (meet a b) a))
    {}))

; A data type for describing lattices
(deftype Lattice [elements join meet]
  ConcreteObject
  (underlying-set [this] elements)

  StructuredLattice
  (join-fn [this] join)
  (meet-fn [this] meet)

  ; The means necessary to make lattices into structured quivers
  StructuredDiset
  (first-set [this] (meet-precedence-relation elements meet))
  (second-set [this] elements)

  StructuredQuiver
  (underlying-quiver [this] (thin-quiver (objects this) (morphisms this)))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver (first-set this) (second-set this) first second (fn [i] (list i i))))
  (identity-morphism-of [this x] (list x x))

  ; Every lattice is a function as a category
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (first-set this))

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Ontology of lattices as categories
(derive Lattice :locus.elementary.copresheaf.core.protocols/lattice)

; We need some special way of getting the underlying relation of lattice
(defmethod underlying-relation Lattice
  [lattice]

  (->SeqableRelation (objects lattice) (morphisms lattice) {}))

(defmethod underlying-multirelation Lattice
  [lattice]

  (underlying-relation lattice))

; We need to be able to have some means of visualizing lattices
(defmethod visualize Lattice
  [lattice]

  (let [object-count (count (objects lattice))]
    (if (= 1 object-count)
      (visualize (underlying-relation lattice))
      (visualize (covering-relation (underlying-relation (underlying-quiver lattice)))))))

; Create a lattice from a relation, with the hopes that the relation
; that you are providing is actually a lattice relation.
(defn relational-lattice
  [rel]
  {:pre [(lattice-relation? rel)]}

  (Lattice.
    (vertices rel)
    (join-operation rel)
    (meet-operation rel)))

; Conversion routines for lattices
(defmulti to-lattice type)

(defmethod to-lattice Lattice
  [lattice] lattice)

(defmethod to-lattice Quiver
  [quiv]

  (if-not (lattice-quiver? quiv)
    (throw (new IllegalArgumentException))
    (let [rel (underlying-relation quiv)]
      (Lattice.
        (objects quiv)
        (join-operation rel)
        (meet-operation rel)))))

(defmethod to-lattice :default
  [rel]

  (relational-lattice rel))

; Join and meet elements of lattice
(defn join-elements
  [lattice & args]

  (apply (join-fn lattice) args))

(defn meet-elements
  [lattice & args]

  (apply (meet-fn lattice) args))

; The partial ordering that defines a lattice
(defn preceding-lattice-elements?
  [lattice a b]

  (= (join-elements lattice a b) b))

; The join and meet functions
(defn join-function
  [lattice]

  (SetFunction.
    (product (underlying-set lattice) (underlying-set lattice))
    (underlying-set lattice)
    (fn [[a b]]
      (join-elements lattice a b))))

(defn meet-function
  [lattice]

  (SetFunction.
    (product (underlying-set lattice) (underlying-set lattice))
    (underlying-set lattice)
    (fn [[a b]]
      (meet-elements lattice a b))))

; Dual lattices
(defmethod dual Lattice
  [^Lattice lattice]

  (Lattice. (underlying-set lattice) (.meet lattice) (.join lattice)))

; The product of lattices is a fundamental operation of lattice theory
(defn lattice-product
  [& lattices]

  (let [l (count lattices)]
    (Lattice.
      (apply cartesian-product (map underlying-set lattices))
      (fn [& colls]
        (map
          (fn [i]
            (apply
              (join-fn (nth lattices i))
              (map
                #(nth % i)
                colls)))
          (range l)))
      (fn [& colls]
        (map
          (fn [i]
            (apply
              (meet-fn (nth lattices i))
              (map
                #(nth % i)
                colls)))
          (range l))))))

(defmethod product :locus.elementary.copresheaf.core.protocols/lattice
  [& args]

  (apply lattice-product args))

; Compute the upper and lower bounds of lattices
; In particular we need these upper and lower bounds when dealing with Heyting algebras
(defn lower-bound-element?
  [lattice lower-bound]

  (every?
    (fn [i]
      (preceding-lattice-elements? lattice lower-bound i))
    (objects lattice)))

(defn upper-bound-element?
  [lattice upper-bound]

  (every?
    (fn [i]
      (preceding-lattice-elements? lattice i upper-bound))
    (objects lattice)))

(defn lower-bound
  [lattice]

  (first
    (filter
      (fn [i]
        (lower-bound-element? lattice i))
      (objects lattice))))

(defn upper-bound
  [lattice]

  (first
    (filter
      (fn [i]
        (upper-bound-element? lattice i))
      (objects lattice))))

; Total order lattices
(defn nth-total-order-lattice
  [n]

  (Lattice.
    (->Upto (inc n))
    max
    min))

(def divisibility-lattice
  (->Lattice
    natural-number?
    lcm
    gcd))

(def naturals-lattice
  (->Lattice
    natural-number?
    max
    min))

(def integers-lattice
  (->Lattice
    integer?
    max
    min))

(def rationals-lattice
  (->Lattice
    rational?
    max
    min))

; A means of dealing with subalgebras of algebraic structures
(defmulti sub type)

; Distributive lattices and total orders of numbers
(defmethod sub java.lang.Integer
  [n] (nth-total-order-lattice n))

(defmethod sub java.lang.Long
  [n] (nth-total-order-lattice n))

(defmethod sub clojure.lang.BigInt
  [n] (nth-total-order-lattice n))

; Distributive lattices of multisets
(defmethod sub Multiset
  [coll]

  (Lattice.
    (power-clan coll)
    join
    meet))

; We also need some means of dealing with congruences of various algebraic structures
(defmulti con type)

; Subalgebras and congruences in the topos Sets
(defmethod sub :default
  [coll]

  (Lattice.
    (power-set coll)
    union
    intersection))

(defmethod con :default
  [coll]

  (Lattice.
    (set-partitions coll)
    join-set-partitions
    meet-set-partitions))

; Subalgebras and congruences in the topos Sets^(->)
(defmethod sub :locus.base.logic.structure.protocols/set-function
  [func]

  (Lattice.
    (all-subalgebras func)
    join-set-pairs
    meet-set-pairs))

(defmethod con :locus.base.logic.structure.protocols/set-function
  [func]

  (Lattice.
    (all-congruences func)
    (fn [& congruences]
      (let [[in out] (apply join-set-pair-congruences congruences)]
        (congruence-closure func in out)))
    meet-set-pair-congruences))

; Ontology of sublattices
(defn sublattice?
  [lattice coll]

  (every?
    (fn [[a b]]
      (and
        (contains? coll (join-elements lattice a b))
        (contains? coll (meet-elements lattice a b))))
    (cartesian-power coll 2)))

(defn sublattice
  [lattice coll]

  (Lattice.
    coll
    (join-fn lattice)
    (meet-fn lattice)))

; Computations with lattices of sublattices
(defn enumerate-sublattices
  [lattice]

  (set
    (filter
      (fn [coll]
        (sublattice? lattice coll))
      (power-set (objects lattice)))))

(defn sublattice-closure
  [lattice coll]

  (let [new-elements (set
                       (apply
                        concat
                        (for [a coll
                              b coll
                              :let [m (meet-elements lattice a b)
                                    j (join-elements lattice a b)]]
                          (list m j))))
        new-set-of-elements (union new-elements coll)]
    (if (equal-universals? coll new-set-of-elements)
      coll
      (sublattice-closure lattice new-set-of-elements))))

(defmethod sub Lattice
  [lattice]

  (Lattice.
    (enumerate-sublattices lattice)
    (fn [& colls]
      (sublattice-closure lattice (apply union colls)))
    intersection))