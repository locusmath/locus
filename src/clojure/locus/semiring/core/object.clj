(ns locus.semiring.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.object :refer :all])
  (:import (locus.elementary.group.core.object Group)
           (locus.elementary.semigroup.core.object Semigroup)))

; Semirings are the most general objects of our algebraic
; ontology. They combine both the associative and the distributive
; laws into a single structure. Rings are a special case. A semiring
; can be constructed from a pair of semigroups (+,*) the first of
; which is necessarily commutative with identity.

(deftype Semiring [elems add mul]
  ConcreteObject
  (underlying-set [this] elems))

(derive Semiring :locus.ring.core.protocols/semiring)

(defmethod additive-semigroup Semiring
  [^Semiring semiring]

  (.add semiring))

(defmethod multiplicative-semigroup Semiring
  [^Semiring semiring]

  (.mul semiring))

(defmethod make-ring :default
  [a b]

  (Semiring. (underlying-set a) a b))

; Ontology of semirings
; Classification of rings and semirings based upon the properties of their
; additive and multiplicative semigroups. The first and foremost level of
; classification is based upon the additive preordeor, which separates semirings
; into additively j trivial semirings and ordinary rings. A similar division occurs
; between semifields, division rings, and fields. A secondary classification is based
; upon commutativity. All of these are determined by properties of the underlying
; additive and multiplicative semigroups of the semirings.
(defn semifield?
  [ring]

  (and
    (semiring? ring)
    (group-with-zero? (multiplicative-semigroup ring))))

(defn commutative-semiring?
  [ring]

  (and
    (semiring? ring)
    (commutative-semigroup? (multiplicative-semigroup ring))))

; Additive j trivial semirings
(defn additively-jtrivial-semiring?
  [semiring]

  (and
    (semiring? semiring)
    (jtrivial? (additive-semigroup semiring))))

(defn idempotent-semiring?
  [ring]

  (and
    (semiring? ring)
    (semilattice? (additive-semigroup ring))))

(defn reduced-semiring?
  [ring]

  (and
    (semiring? ring)
    (reduced-semigroup-with-zero? (multiplicative-semigroup ring))))

; Additively J total semirings
(defmethod ring? :locus.ring.core.protocols/semiring
  [semiring]

  (group? (additive-semigroup semiring)))

(defn reduced-ring?
  [ring]

  (and
    (ring? ring)
    (reduced-semigroup-with-zero? (multiplicative-semigroup ring))))

(defn commutative-ring?
  [ring]

  (and
    (ring? ring)
    (commutative-semigroup? (multiplicative-semigroup ring))))

(defn domain?
  [ring]

  (and
    (ring? ring)
    (semigroup-with-adjoined-zero? (multiplicative-semigroup ring))))

(defn integral-domain?
  [ring]

  (and
    (ring? ring)
    (commutative-monoid-with-adjoined-zero? (multiplicative-semigroup ring))))

(defn division-ring?
  [ring]

  (and
    (ring? ring)
    (group-with-zero? (multiplicative-semigroup ring))))

(defn field?
  [ring]

  (and
    (ring? ring)
    (commutative-group-with-zero? (multiplicative-semigroup ring))))

(defn von-neumann-regular-ring?
  [ring]

  (and
    (ring? ring)
    (regular-semigroup? (multiplicative-semigroup ring))))

(defn boolean-ring?
  [ring]

  (and
    (semiring? ring)
    (boolean-group? (additive-semigroup ring))))

; Special classes of rings
(defn ring-with-identity?
  [ring]

  (and
    (ring? ring)
    (monoid? (multiplicative-semigroup ring))))

(defn semiring-with-identity?
  [ring]

  (and
    (semiring? ring)
    (monoid? (multiplicative-semigroup ring))))

; Additively J-trivial semirings
(def nn
  (make-ring natural-addition natural-multiplication))

(def qt
  (make-ring nonnegative-rational-addition nonnegative-rational-multiplication))

; Total order semirings
(defn total-order-semiring
  [n]

  (make-ring
    (max-monoid n)
    (min-monoid n)))

(def t2
  (total-order-semiring 2))

(def t3
  (total-order-semiring 3))

(def t4
  (total-order-semiring 4))

; Distributive lattice semirings
(defn distributive-lattice->semiring
  [lattice]

  (make-ring
    (to-monoid (join-semilattice lattice))
    (meet-semilattice lattice)))

(defn power-set-semiring
  [coll]

  (let [elems (->PowerSet coll)]
    (->Semiring
      elems
      (->Monoid elems (fn [[a b]] (union a b)) #{})
      (->Monoid elems (fn [[a b]] (intersection a b)) coll))))

(defn family-semiring
  [family]

  (make-ring
    (->Monoid
      family
      (fn [[a b]] (union a b))
      (first (minimal-members family)))
    (->Semigroup family (fn [[a b]] (intersection a b)))))

; Semiring theoretic methods of category theory
(defn semiring-of-morphism-systems
  [semigroupoid]

  (let [coll (morphisms semigroupoid)]
    (make-ring
      (power-set-union-monoid coll)
      (semigroup-of-sets-of-morphisms coll))))

; Products of semirings
(defmethod product Semiring
  [& semirings]

  (->Semiring
    (apply product (map underlying-set semirings))
    (apply product (map additive-semigroup semirings))
    (apply product (map multiplicative-semigroup semirings))))

; Subsemirings
(defn subsemiring?
  [semiring coll]

  (and
    (identity-preserving-subsemigroup? (additive-semigroup semiring) coll)
    (subsemigroup? (multiplicative-semigroup semiring) coll)))

(defn subsemirings
  [semiring]

  (set
    (filter
      (fn [coll]
        (subsemiring? semiring coll))
      (power-set (underlying-set semiring)))))

(defmethod sub Semiring
  [semiring]

  (if (intrinsic-group? (additive-semigroup semiring))
    (->Lattice (subrings semiring) union intersection)
    (->Lattice (subsemirings semiring) union intersection)))

(defn restrict-semiring
  [semiring coll]

  (Semiring.
    coll
    (restrict-semigroup (additive-semigroup semiring) coll)
    (restrict-semigroup (multiplicative-semigroup semiring) coll)))

; Semiring congruences
(defn semiring-congruence?
  [semiring partition]

  (and
    (semigroup-congruence? (additive-semigroup semiring) partition)
    (semigroup-congruence? (multiplicative-semigroup semiring) partition)))

(defn semiring-congruences
  [semiring]

  (set
    (filter
      (fn [partition]
        (semiring-congruence? semiring partition))
      (set-partitions (set (underlying-set semiring))))))

(defmethod con Semiring
  [semiring]

  (if (intrinsic-group? (additive-semigroup semiring))
    (->Lattice
      (ring-ideals semiring)
      union
      intersection)
    (->Lattice
      (semiring-congruences semiring)
      join-set-partitions
      meet-set-partitions)))

(defn quotient-semiring
  [semiring partition]

  (Semiring.
    partition
    (quotient-semigroup semiring partition)
    (quotient-semigroup semiring partition)))

; The fundamental idea of a semiring of ideals
(defn semiring-of-ideals
  [ring]

  (let [coll (ring-ideals ring)
        add (additive-semigroup ring)
        mul (multiplicative-semigroup ring)]
    (Semiring.
      coll
      (->Monoid
        coll
        (fn [[a b]] (subsemigroup-closure add (union a b)))
        #{})
      (->Semigroup
        coll
        (fn [[a b]]
          (compose-subsets mul a b))))))

