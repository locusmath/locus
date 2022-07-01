(ns locus.elementary.lattice.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.nms :refer :all]
            [locus.elementary.logic.base.sig :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.signatures.nf :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.gem.core.object :refer :all])
  (:import (locus.elementary.relation.binary.sr SeqableRelation)
           (locus.elementary.quiver.core.object Quiver)
           (locus.elementary.diset.core.object Diset)
           (locus.elementary.function.core.object SetFunction)
           (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.logic.base.core Multiset)
           (locus.elementary.difunction.core.object Difunction)
           (locus.elementary.gem.core.object Gem)))

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
  (first-set [this] (join-precedence-relation elements join))
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
  (outputs [this])

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Ontology of lattices as categories
(derive Lattice :locus.elementary.function.core.protocols/lattice)

; We need to be able to have some means of visualizing lattices
(defmethod visualize Lattice
  [lattice]

  (let [object-count (count (objects lattice))]
    (if (= 1 object-count)
      (visualize (underlying-relation lattice))
      (visualize (covering-relation (underlying-relation (underlying-quiver lattice)))))))

; Conversion routines for lattices
(defmulti to-lattice type)

(defmethod to-lattice Lattice
  [lattice] lattice)

; Create a lattice from a relation, with the hopes that the relation
; that you are providing is actually a lattice relation.
(defn relational-lattice
  [rel]
  {:pre [(lattice-relation? rel)]}

  (Lattice.
    (vertices rel)
    (join-operation rel)
    (meet-operation rel)))

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

; We need some special way of getting the underlying relation of lattice
(defmethod underlying-relation Lattice
  [lattice]

  (first-set lattice))

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

(defmethod product :locus.elementary.function.core.protocols/lattice
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

; Intervals lattice
(defn join-intervals*
  [pair1 pair2]

  (cond
    (empty? pair1) pair2
    (empty? pair2) pair1
    :else (let [[a b] pair1
                [c d] pair2]
            [(min a c)
             (max b d)])))

(defn meet-intervals*
  [pair1 pair2]

  (cond
    (empty? pair1) []
    (empty? pair2) []
    :else (let [[a b] pair1
                [c d] pair2]
            (let [new-start (max a c)
                  new-end (min b d)]
              (if (<= new-start new-end)
                [new-start new-end]
                [])))))

(defn interval-lattice
  [n]

  (Lattice.
    (all-intervals n)
    (monoidalize join-intervals*)
    (monoidalize meet-intervals*)))

; Noncrossing partition lattice
(defn noncrossing-partition-lattice
  [n]

  (Lattice.
    (set
      (filter
        noncrossing-range-partition?
        (set-partitions (set (range n)))))
    join-noncrossing-partitions
    meet-set-partitions))

; Compute the lattice of preorders of a set
(defn lattice-of-preorders
  [coll]

  (Lattice.
    (fn [x]
      (and
        (preorder? x)
        (= (vertices x) coll)))
    (fn [& args]
      (cl transitive? (apply union args)))
    intersection))

; Total order lattices
(defn nth-total-order-lattice
  [n]

  (Lattice.
    (seqable-interval 0 (inc n))
    max
    min))

; Get a lattice from a Moore family and its closure operation
(defn moore-lattice
  [family]

  (Lattice.
    (dimembers family)
    (fn [& args]
      (cl family (apply union args)))
    intersection))

; Youngs lattice of additive partitions
(def youngs-lattice
  (Lattice.
    additive-partition?
    young-join
    young-meet))

; We now need some way of dealing with subalgebras
(defmulti sub type)

(defmethod sub java.lang.Integer
  [n] (nth-total-order-lattice n))

(defmethod sub java.lang.Long
  [n] (nth-total-order-lattice n))

(defmethod sub clojure.lang.BigInt
  [n] (nth-total-order-lattice n))

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

; Subalgebras and congruences in the topos Sets^2
(defmethod sub Diset
  [pair]

  (Lattice.
    (seqable-diset-subalgebras pair)
    join-set-pairs
    meet-set-pairs))

(defmethod con Diset
  [pair]

  (Lattice.
    (seqable-diset-congruences pair)
    join-set-pair-congruences
    meet-set-pair-congruences))

; Subalgebras and congruences in the topos Sets^(->)
(defmethod sub :locus.elementary.function.core.protocols/set-function
  [func]

  (Lattice.
    (all-subalgebras func)
    join-set-pairs
    meet-set-pairs))

(defmethod con :locus.elementary.function.core.protocols/set-function
  [func]

  (Lattice.
    (all-congruences func)
    (fn [& congruences]
      (let [[in out] (apply join-set-pair-congruences congruences)]
        (congruence-closure func in out)))
    meet-set-pair-congruences))

; Subalgebras and congruences of bijections
(defmethod sub Bijection
  [func]

  (Lattice.
    (all-subbijections func)
    join-set-pairs
    meet-set-pairs))

(defmethod con Bijection
  [func]

  (Lattice.
    (set (bijection-congruences func))
    (fn [& congruences]
      (let [[in out] (apply join-set-pair-congruences congruences)]
        (congruence-closure func in out)))
    meet-set-pair-congruences))

; Subalgebras and congruences of quivers
(defmethod sub :locus.elementary.quiver.core.object/quiver
  [quiv]

  (Lattice.
    (subquivers quiv)
    join-set-pairs
    meet-set-pairs))

(defmethod con :locus.elementary.quiver.core.object/quiver
  [quiv]

  (Lattice.
    (quiver-congruences quiv)
    join-set-pair-congruences
    meet-set-pair-congruences))

; Subalgebras and congruencse of difunctions
(defmethod sub Difunction
  [x]

  (product
    (sub (first-function x))
    (sub (second-function x))))

(defmethod con Difunction
  [x]

  (product
    (con (first-function x))
    (con (second-function x))))

; Subalgebras and congruences of morphisms of bijections
(defmethod sub Gem
  [gem]

  (sub (interrelational-component gem)))

(defmethod con Gem
  [gem]

  (con (interrelational-component gem)))

; Subalgebra lattices of lattices
(defn enumerate-sublattices
  [lattice]

  (set
    (filter
      (fn [coll]
        (every?
          (fn [[a b]]
            (and
              (contains? coll (join-elements lattice a b))
              (contains? coll (meet-elements lattice a b))))
          (cartesian-product coll coll)))
      (power-set (underlying-set lattice)))))

(defmethod sub Lattice
  [lattice]

  (Lattice.
    (enumerate-sublattices lattice)
    union
    intersection))

(defn restrict-lattice
  [lattice coll]

  (Lattice.
    coll
    (join-fn lattice)
    (meet-fn lattice)))

; The subobject lattice of a set relation
(comment
  (defmethod sub SetRelation
    [rel]

    (->Lattice
      (set (enumerate-set-subrelations rel))
      join-set-pairs
      meet-set-pairs)))