(ns locus.additive.semiring.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]))

; Semirings are like semiringoids with a single object
; In other words, they are like CMon-enriched categories with a single object. They are the
; most general elements of our additive ontology of arithmetically enriched categories and
; semigroupoids. Semirings are distinguished by how they combine associative and distributive
; laws into a single structure. Rings, fields, and semifields are special cases determined
; by divisibility properties. A semiring can always be formed by a pair of semigroups that
; distribute over each other.

(deftype Semiring [elems add mul]
  ConcreteObject
  (underlying-set [this] elems))

(derive Semiring :locus.additive.base.core.protocols/semiring)

(defmethod additive-semigroup Semiring
  [^Semiring semiring]

  (.add semiring))

(defmethod multiplicative-semigroup Semiring
  [^Semiring semiring]

  (.mul semiring))

; Constructor for semirings
; The default case for two given semigroups is that they should be used to construct a semiring.
; We only go out of our way to construct rings, fields, and semifields provided that we notice
; special datatypes like groups and groups with zero in the arguments to the function.
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
(defmulti field? type)

(defmethod field? :locus.additive.base.core.protocols/skew-field
  [skew-field]

  (commutative-semigroup? (multiplicative-semigroup skew-field)))

(defmethod field? :default
  [structure]

  (and
    (semiring? structure)
    (group? (additive-semigroup structure))
    (commutative-group-with-zero? (multiplicative-semigroup structure))))

(defmulti semifield? type)

(defmethod semifield? :locus.additive.base.core.protocols/skew-semifield
  [skew-semifield]

  (commutative-semigroup? (multiplicative-semigroup skew-semifield)))

(defmethod semifield? :default
  [structure]

  (and
    (semiring? structure)
    (commutative-group-with-zero? (multiplicative-semigroup structure))))

; Reduced semirings
(defn reduced-semiring?
  [ring]

  (and
    (semiring? ring)
    (reduced-semigroup-with-zero? (multiplicative-semigroup ring))))

(defn von-neumann-regular-semiring?
  [ring]

  (and
    (semiring? ring)
    (regular-semigroup? (multiplicative-semigroup ring))))

; Additive j trivial semirings
(defn additively-jtrivial-semiring?
  [semiring]

  (and
    (semiring? semiring)
    (jtrivial? (additive-semigroup semiring))))

(defn commutative-additively-jtrivial-semiring?
  [semiring]

  (and
    (semiring? semiring)
    (jtrivial? (additive-semigroup semiring))
    (commutative-semigroup? (multiplicative-semigroup semiring))))

(defn idempotent-semiring?
  [ring]

  (and
    (semiring? ring)
    (semilattice? (additive-semigroup ring))))

(defn commutative-idempotent-semiring?
  [ring]

  (and
    (semiring? ring)
    (semilattice? (additive-semigroup ring))
    (commutative-semigroup? (multiplicative-semigroup ring))))

(defn multiplicatively-idempotent-semiring?
  [ring]

  (and
    (semiring? ring)
    (band? (multiplicative-semigroup ring))))

(defn multiplicatively-idempotent-commutative-semiring?
  [ring]

  (and
    (semiring? ring)
    (semilattice? (multiplicative-semigroup ring))))

(defn dually-idempotent-semiring?
  [ring]

  (and
    (semiring? ring)
    (semilattice? (additive-semigroup ring))
    (band? (multiplicative-semigroup ring))))

(defn dually-idempotent-commutative-semiring?
  [ring]

  (and
    (semiring? ring)
    (semilattice? (additive-semigroup ring))
    (semilattice? (multiplicative-semigroup ring))))

; Additively j trivial semifields
(defn additively-jtrivial-skew-semifield?
  [semiring]

  (and
    (skew-semifield? semiring)
    (jtrivial? (additive-semigroup semiring))))

(defn additively-jtrivial-semifield?
  [semiring]

  (and
    (semifield? semiring)
    (jtrivial? (additive-semigroup semiring))))

; Additively J total semirings
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

; The fundamental semiring
(def nn
  (make-ring natural-addition natural-multiplication))

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

  (->Lattice
    (subsemirings semiring)
    union
    intersection))

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

  (->Lattice
    (semiring-congruences semiring)
    join-set-partitions
    meet-set-partitions))

(defn quotient-semiring
  [semiring partition]

  (Semiring.
    partition
    (quotient-semigroup semiring partition)
    (quotient-semigroup semiring partition)))