(ns locus.elementary.group.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.natural :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)
           (locus.elementary.function.core.object SetFunction)
           (locus.elementary.semigroup.monoid.object Monoid)
           (locus.elementary.semigroup.core.object Semigroup)))

; A group is a single object category for which every morphism is an isomorphism. Equivalently, it
; can be defined as a single object groupoid. Every single group can be defined as a monoid
; which is also equipped with an inversion function. The map to the inversion function is a
; copresheaf-valued functor to Sets^(->).
(deftype Group [elems op id inv]
  ConcreteObject
  (underlying-set [this] elems)

  ; Semigroups are semigroupoids and so they are structured quivers
  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (singular-unital-quiver elems 0 id))
  (identity-morphism-of [this obj] id)

  StructuredPermutableQuiver
  (invert-morphism [this x]
    (inv x))
  (underlying-permutable-quiver [this]
    (singular-permutable-quiver elems 0 inv))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this]
    (singular-dependency-quiver elems 0 id inv))

  ; Every semigroup is a function
  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; A special method for inverting elements of groups
(defmethod invert-element Group
  [^Group group, x] ((.inv group) x))

; Tagging groups
(derive Group :locus.elementary.function.core.protocols/group)

; This makes getting the identity element of a group easier
(defmethod identity-elements Group
  [sgrp]

  #{(.id sgrp)})

; Convert semigroups and monoids into groups
; Although basically the same mathematically, these different kinds of semigroupoid
; can be represented using different data structures. In order to address that
; we provide conversion routines for converting group like objects into instances
; of the group class.
(defmulti to-group type)

(defmethod to-group Monoid
  [^Monoid monoid]

  (Group.
    (.elems monoid)
    (.op monoid)
    (.id monoid)
    (fn [elem]
      (first (find-element-inverses monoid (.id monoid) elem)))))

(defmethod to-group Semigroup
  [^Semigroup semigroup]

  (let [identities (identity-elements semigroup)]
    (when (not (empty? identities))
      (let [id (first identities)]
        (Group.
         (.elems semigroup)
         (.op semigroup)
         id
         (fn [elem]
           (first (find-element-inverses semigroup id elem))))))))

(defmethod to-group SetFunction
  [func] (to-group (to-semigroup func)))

; Create a group by a table
(defn group-by-table
  [coll]

  (to-group (semigroup-by-table coll)))

; Get the inverse bijection associated with a group
(defmethod inverse-function Group
  [^Group group]

  (->SetFunction
    (underlying-set group)
    (underlying-set group)
    (fn [elem]
      ((.inv group) elem))))

; Cyclic groups
(defn cyclic-group
  [period]

  (Group.
    (seqable-interval 1 (inc period))
    (fn [[a b]]
      (monogenic-simplification 1 period (+ a b)))
    period
    (fn [elem]
      (if (= elem period)
        period
        (- period elem)))))

; Finitely generated commutative groups have been fully classified
(defn finitely-generated-commutative-group
  [& nums]

  (let [n (count nums)]
    (Group.
     (apply
       seqable-cartesian-product
       (map
         (fn [i]
           (seqable-interval 0 i))
         nums))
     (fn [[coll1 coll2]]
       (map
         (fn [i]
           (mod (+ (nth coll1 i) (nth coll2 i)) (nth nums i)))
         (range n)))
     (repeat n 0)
     (partial map -))))

(defn boolean-group
  [n]

  (apply finitely-generated-commutative-group (repeat n 2)))

; Symmetric groups
(defn nth-symmetric-group
  [n]

  (Group.
    (enumerate-sequence-permutations (range n))
    (fn [[a b]]
      (map
        (fn [i]
          (nth a (nth b i)))
        (range n)))
    (range n)
    (fn [perm]
      (map
        (fn [i]
          (.indexOf perm i))
        (range n)))))

; Product operation
; The product of two groups is a group again
(defmethod product :locus.elementary.function.core.protocols/group
  [& monoids]

  (Group.
    (apply cartesian-product (map underlying-set monoids))
    (apply semigroup-product-function monoids)
    (map #(.id %) monoids)
    (fn [obj]
      (map-indexed
        (fn [i v]
          ((.inv ^Group (nth monoids i)) v))
        obj))))

; The index of a subgroup determined by Lagrange's theorem
(defn subgroup-index
  [group coll]

  (/ (count (underlying-set group))
     (count coll)))

; Subalgebra lattices
; This should take advantage of Lagrange's theorem eventually
(defn subgroup?
  [group coll]

  (and
    (group? group)
    (identity-preserving-subsemigroup? group coll)))

(defn all-subgroups
  [group]

  (let [possible-subgroups (lagrange-interval (identity-elements group) (underlying-set group))
        actual-subgroups (set
                           (filter
                             (partial subsemigroup? group)
                             possible-subgroups))]
    actual-subgroups))

(defn proper-subgroups
  [group]

  (disj (all-subgroups group) (set (underlying-set group))))

(defn maximal-proper-subgroups
  [group]

  (maximal-members (proper-subgroups group)))

(defn nontrivial-subgroups
  [group]

  (disj (all-subgroups group) (identity-elements group)))

(defn minimal-nontrivial-subgroups
  [group]

  (minimal-members (nontrivial-subgroups group)))

(defmethod sub :locus.elementary.function.core.protocols/group
  [group]

  (Lattice.
    (all-subgroups group)
    (comp (partial subsemigroup-closure group) union)
    intersection))

(defn restrict-group
  [^Group group, coll]

  (Group.
    coll
    (.op group)
    (.id group)
    (.inv group)))

; Compute the dual of a group
(defmethod dual :locus.elementary.function.core.protocols/group
  [group]

  (Group.
    (underlying-set group)
    (fn [pair]
      (group (reverse pair)))
    (.id group)
    (.inv group)))

; Left cosets
(defn left-coset-of
  [group coll elem]

  (set
    (map
      (fn [i]
        (group (list i elem)))
      coll)))

(defn left-cosets
  [group coll]

  (loop [rval #{}
         remaining-elements (set (underlying-set group))]
    (if (empty? remaining-elements)
      rval
      (let [current-element (first remaining-elements)
            current-coset (left-coset-of group coll current-element)]
        (recur
          (conj rval current-coset)
          (difference remaining-elements current-coset))))))

(defn right-coset-of
  [group coll elem]

  (set
    (map
      (fn [i]
        (group (list elem i)))
      coll)))

(defn right-cosets
  [group coll]

  (loop [rval #{}
         remaining-elements (set (underlying-set group))]
    (if (empty? remaining-elements)
      rval
      (let [current-element (first remaining-elements)
            current-coset (right-coset-of group coll current-element)]
        (recur
          (conj rval current-coset)
          (difference remaining-elements current-coset))))))

(defn normal-subgroup?
  [group coll]

  (and
    (identity-preserving-subsemigroup? group coll)
    (= (left-cosets group coll)
       (right-cosets group coll))))

(defn normal-subgroups
  [group]

  (set
    (filter
      (partial normal-subgroup? group)
      (all-subgroups group))))

(defn proper-normal-subgroups
  [group]

  (disj (normal-subgroups group) (underlying-set group)))

(defn nontrivial-normal-subgroups
  [group]

  (disj (normal-subgroups group) (identity-elements group)))

(defn minimal-nontrivial-normal-subgroups
  [group]

  (minimal-members (nontrivial-normal-subgroups group)))

(defn maximal-proper-normal-subgroups
  [group]

  (maximal-members (proper-normal-subgroups group)))

(defmethod con :locus.elementary.function.core.protocols/group
  [group]

  (Lattice.
    (normal-subgroups group)
    (comp (partial subsemigroup-closure group) union)
    intersection))

(defn quotient-group
  [group partition]

  (Group.
    partition
    (fn [[c1 c2]]
      (projection partition (group (list (first c1) (first c2)))))
    (projection partition (first (identity-elements group)))
    (fn [part]
      (projection partition ((.inv group) (first part))))))

(defn normal-subgroup->congruence
  [group coll]

  (left-cosets group coll))

(defn quotient-group-by-normal-subgroup
  [group coll]

  (quotient-group group (normal-subgroup->congruence group coll)))

; Conjugacy classes of elements
(defn right-conjugate
  [group g x]

  (apply-semigroup
    group
    (list ((.inv group) g) x g)))

(defn left-conjugate
  [group g x]

  (apply-semigroup
    group
    (list g x ((.inv group) g))))

(defn conjugacy-class
  [group x]

  (set
    (map
      (fn [i]
        (left-conjugate group i x))
      (underlying-set group))))

(defn conjugacy-classes
  [group]

  (loop [remaining-elements (underlying-set group)
         rval #{}]
    (if (empty? remaining-elements)
      rval
      (let [current-class (conjugacy-class group (first remaining-elements))]
        (recur
          (difference remaining-elements current-class)
          (conj rval current-class))))))

(defn conjugacy-class-size-statistics
  [group]

  (multiset (map count (conjugacy-classes group))))

; Conjugacy classes of subgroups
(defn left-conjugate-subgroup
  [group g coll]

  (set
    (map
      (fn [i]
        (left-conjugate group g i))
      coll)))

(defn right-conjugate-subgroup
  [group g coll]

  (set
    (map
      (fn [i]
        (right-conjugate group g i))
      coll)))

(defn subgroup-conjugacy-class
  [group coll]

  (set
    (map
      (fn [i]
        (left-conjugate-subgroup group i coll))
      (underlying-set group))))

(defn subgroup-conjugacy-classes
  [group]

  (loop [remaining-subgroups (all-subgroups group)
         rval #{}]
    (if (empty? remaining-subgroups)
      rval
      (let [next-subgroup (first remaining-subgroups)
            next-class (subgroup-conjugacy-class group next-subgroup)]
        (recur
          (difference remaining-subgroups next-class)
          (conj rval next-class))))))

; Get the group of units of a semigroup
(defmulti group-of-units type)

(defmethod group-of-units Group
  [group] group)

(defmethod group-of-units :default
  [semigroup]

  (let [identities (identity-elements semigroup)]
    (when (not (empty? identities))
      (let [identity-element (first identities)]
        (Group.
          (unit-elements semigroup)
          semigroup
          identity-element
          (fn [elem]
            (first (find-element-inverses semigroup identity-element elem))))))))

; Derived subgroups
(defn commutator
  [group x y]

  (apply-semigroup
    group
    (list x y ((.inv group) x) ((.inv group) y))))

(defn commutator-compositions
  [group]

  (let [all-commutators (map
                          (fn [[x y]]
                            (commutator group x y))
                          (cartesian-power (underlying-set group) 2))]
    (subsemigroup-closure group all-commutators)))

(defn derived-subgroup
  [group]

  (restrict-group group (commutator-compositions group)))

(defn abelianization
  [group]

  (quotient-group group (commutator-compositions group)))

(defn derived-series
  [group]

  (loop [rval [group]
         current-group group]
    (let [next-group (derived-subgroup current-group)]
      (if (= (semigroup-size next-group) (semigroup-size current-group))
        rval
        (recur
          (conj rval next-group)
          next-group)))))

(defn derived-length
  [group]

  (count (derived-series group)))

; Special subgroups
(defn trivial-subgroup
  [group]

  (restrict-group group (identity-elements group)))

(defn frattini-subgroup
  [group]

  (restrict-group group (apply intersection (maximal-proper-subgroups group))))

(defn socle
  [group]

  (let [subgroups (minimal-nontrivial-normal-subgroups group)
        elems (subsemigroup-closure group (apply union subgroups))]
    (restrict-group group elems)))

(defn baer-radical
  [group]

  (restrict-group group (apply intersection (maximal-proper-normal-subgroups group))))

; Get the order of an element of a torsion group
(defn group-element-order
  [group x]

  (let [identity (first (identity-elements group))]
    (loop [current-elem x
           n 1]
      (if (= current-elem identity)
        n
        (recur
          (group (list current-elem x))
          (inc n))))))

(defn order-statistics
  [group]

  (map
    (fn [i]
      (group-element-order group i))
    (underlying-set group)))

; The exponent is the lcm of all group element orders
(defn group-exponent
  [group]

  (apply lcm (order-statistics group)))

; Ontology of groups
; The ontology of groups generally proceeds from the ontology of monoids. From that
; perspective groups are special single object categories, and so generalizing out
; further they are a part of the ontology of categories. Then the ontology of
; groups further reduces them to a number of special classes.
(defn dedekind-group?
  [group]

  (every?
    (fn [i]
      (normal-subgroup? group i))
    (all-subgroups group)))

(defn pgroup?
  [group]

  (and
    (group? group)
    (prime-power? (count (underlying-set group)))))

(defn cyclic-pgroup?
  [group]

  (intersection
    cyclic-group?
    pgroup?))

(defn prime-group?
  [group]

  (and
    (group? group)
    (prime-number? (count (underlying-set group)))))

(defn simple-group?
  [group]

  (<= (count (normal-subgroups group)) 2))

(defn perfect-group?
  [group]

  (= (underlying-set group) (commutator-compositions group)))

(defn solvable-group?
  [group]

  (let [series (derived-series group)]
    (= (semigroup-size (last series)) 1)))

(defn metacommutative-group?
  [group]

  (commutative-group? (derived-subgroup group)))

(defn metacyclic-group?
  [group]

  (let [h (derived-subgroup group)]
    (and
      (cyclic-group? h)
      (cyclic-group? (quotient-group-by-normal-subgroup group (underlying-set h))))))

(defn elementary-commutative-group?
  [group]

  (and
    (commutative-group? group)
    (let [nontrivial-orders (map
                              (partial group-element-order group)
                              (difference (underlying-set group) (identity-elements group)))]
      (equal-seq? nontrivial-orders))))

(defn boolean-group?
  [group]

  (and
    (commutative-group? group)
    (every?
      (fn [i]
        (let [order (group-element-order group i)]
          (or
            (= order 1)
            (= order 2))))
      (underlying-set group))))

(defn frattini-free-group?
  [group]

  (and
    (group? group)
    (= (semigroup-size (frattini-subgroup group)) 1)))














