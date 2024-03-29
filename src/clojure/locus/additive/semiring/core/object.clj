(ns locus.additive.semiring.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]))

; Semirings are semiringoids with a single object
; In other words, they are CMon-enriched categories with a single object. They are the
; most general elements of our additive ontology of arithmetically enriched categories and
; semigroupoids. Semirings are distinguished by how they combine associative and distributive
; laws into a single structure. Rings, fields, and semifields are special cases determined
; by divisibility properties. A semiring can always be formed by a pair of semigroups that
; distribute over each other.

(deftype Semiring [elems add mul]
  ConcreteObject
  (underlying-set [this] elems)

  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (mul obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Semiring :locus.additive.base.core.protocols/semiring)

; Underlying relations and multirelations for semirings
(defmethod underlying-multirelation Semiring
  [^Semiring semiring] (underlying-multirelation (underlying-quiver semiring)))

(defmethod underlying-relation Semiring
  [^Semiring semiring] (set (underlying-multirelation semiring)))

(defmethod visualize Semiring
  [^Semiring semiring] (visualize (underlying-quiver semiring)))

; Get the additive or multiplicative semigroups of a semiring
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