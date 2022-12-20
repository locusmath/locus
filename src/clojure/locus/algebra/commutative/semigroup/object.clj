(ns locus.algebra.commutative.semigroup.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.con.core.setpart :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all])
  (:import (java.util Optional)))

; A commutative semigroup is a naturally preordered algebraic structure. The preordering on the
; commutative semigroup is defined by the Green's J relation, which coincides with all the other
; Green preorders by commutativity. By the universality of condensation, every commutative
; semigroup can be condensed to form a commutative J-trivial semigroup by taking the quotient
; of the commutative semigroup by the congruence formed by strongly connected components. This
; produces a strong relationship between order theory and commutative semigroup theory.

(deftype CommutativeSemigroup [elems rel op]
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
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive CommutativeSemigroup :locus.set.copresheaf.structure.core.protocols/commutative-semigroup)

(def s1*
  (CommutativeSemigroup.
    #{0 1 2}
    (total-order 0 1 2)
    (fn [[a b]]
      (min (+ a b) 2))))

(def s2*
  (CommutativeSemigroup.
    #{0 1 2 3}
    (total-preorder [#{0 1} #{2 3}])
    (fn [[a b]]
      (get-in [[0 1 2 3]
               [1 0 3 2]
               [2 3 2 3]
               [3 2 3 2]]
              [a b]))))

; Conversion routines for commutative semigroups
(defmulti to-commutative-semigroup type)

(defmethod to-commutative-semigroup CommutativeSemigroup
  [^CommutativeSemigroup semigroup] semigroup)

; A useful utility function for semigroups
(defn apply-semigroup
  [func coll]

  (if (= (count coll) 1)
    (first coll)
    (reduce
      (fn [a b]
        (func (list a b)))
      coll)))

; Identity elements for commutative semigroups
(defn two-sided-identity-element?
  [semigroup identity-element]

  (every?
    (fn [i]
      (= i
         (semigroup (list identity-element i))
         (semigroup (list i identity-element))))
    (morphisms semigroup)))

(defmethod identity-elements :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [semigroup]

  (filter
    (fn [morphism]
      (every?
        (fn [i]
          (= (semigroup (list morphism i)) i))
        (morphisms semigroup)))
    (morphisms semigroup)))

(defmethod identity-elements :default
  [semigroup]

  (set
    (filter
      (fn [i]
        (two-sided-identity-element? semigroup i))
      (morphisms semigroup))))

(defn identity-element
  [monoid]

  (first (identity-elements monoid)))

(defn optional-identity
  [semigroup]

  (let [identities (identity-elements semigroup)]
    (if (empty? identities)
      (Optional/empty)
      (Optional/of (first identities)))))

; Zero elements for commutative semigroups
(defn zero-element?
  [semigroup zero-element]

  (every?
    (fn [i]
      (= zero-element
         (semigroup (list i zero-element))
         (semigroup (list zero-element i))))
    (morphisms semigroup)))

(defmethod zero-elements :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [semigroup]

  (filter
    (fn [morphism]
      (every?
        (fn [i]
          (= (semigroup (list morphism i)) morphism))
        (morphisms semigroup)))
    (morphisms semigroup)))

(defmethod zero-elements :default
  [semigroup]

  (set
    (filter
      (fn [zero-element]
        (zero-element? semigroup zero-element))
      (morphisms semigroup))))

(defn zero-element
  [semigroup]

  (first (zero-elements semigroup)))

(defn optional-zero
  [semigroup]

  (let [zeros (zero-elements semigroup)]
    (if (empty? zeros)
      (Optional/empty)
      (Optional/of (first zeros)))))

; The dual operation for commutative semigroups is trivial
(defmethod dual :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [commutative-semigroup] commutative-semigroup)

; Get the natural preorder of a commutative semigroup
(defmethod natural-preorder CommutativeSemigroup
  [^CommutativeSemigroup semigroup] (.-rel semigroup))

(defn natural-preposet
  [semigroup]

  (->Preposet
    (morphisms semigroup)
    (natural-preorder semigroup)))

(defn natural-predecessor?
  [semigroup a b]

  ((natural-preorder semigroup) (list a b)))

(defn enumerate-natural-preorder
  [semigroup]

  (let [rel (natural-preorder semigroup)]
    (set
      (filter
        (fn [[a b]]
          (rel (list a b)))
        (cartesian-power (morphisms semigroup) 2)))))

; The strong connectivity congruence of a commutative semigroup
(defn naturally-strongly-connected-component-of
  [semigroup x]

  (let [rel (natural-preorder semigroup)]
    (set
      (filter
       (fn [y]
         (and
           (rel (list x y))
           (rel (list y x))))
       (morphisms semigroup)))))

(defn naturally-strongly-connected-components
  [semigroup]

  (let [rel (natural-preorder semigroup)]
    (loop [current-elements (set (morphisms semigroup))
           current-components #{}]
      (if (empty? current-elements)
        current-components
        (let [current-element (first current-elements)
              current-component (naturally-strongly-connected-component-of semigroup current-element)]
          (recur
            (difference current-elements current-component)
            (conj current-components current-component)))))))

; The natural condensation of a commutative semigroup
(defmulti natural-condensation type)

(defmethod natural-condensation CommutativeSemigroup
  [commutative-semigroup]

  (let [components (vec (naturally-strongly-connected-components commutative-semigroup))
        size (count components)
        underlying-rel (natural-preorder commutative-semigroup)
        rel (set
              (for [i (range size),
                    j (range size)
                    :let [ic (nth components i)
                          jc (nth components j)
                          a (first ic)
                          b (first jc)]
                    :when (underlying-rel (list a b))]
                (list i j)))
        table (vec
                (map
                  (fn [y]
                    (vec
                      (map
                        (fn [x]
                          (let [a (first (nth components y))
                                b (first (nth components x))
                                ab (commutative-semigroup (list a b))]
                            (index-of-container? components ab)))
                        (range size))))
                  (range size)))]
    (->CommutativeSemigroup
      (->Upto size)
      rel
      (fn [[a b]]
        (get-in table [a b])))))

; Ideals theory for commutative semigroups
(defn natural-ideals
  [commutative-semigroup]

  (filters (filters (natural-preorder commutative-semigroup))))

; Divisibility relations in naturally preordered commutative semigroups
(defn algebraic-divisors
  [semigroup x]

  (let [rel (natural-preorder semigroup)]
    (set
     (filter
       (fn [morphism]
         (rel (list morphism x)))
       (morphisms semigroup)))))

(defn pairwise-algebraic-divisors
  [semigroup a b]

  (set
    (filter
      (fn [i]
        (= (semigroup (list a i)) b))
      (morphisms semigroup))))

; Get the list of all inverses of a semigroup element
(defmulti inverse-elements (fn [semigroup element] (type semigroup)))

(defmethod inverse-elements :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [commutative-semigroup x]

  (let [identities (identity-elements commutative-semigroup)]
    (if (empty? identities)
      '()
      (let [identity-element (first identities)]
        (pairwise-algebraic-divisors commutative-semigroup x identity-element)))))

(defmulti invert-element (fn [semigroup element] (type semigroup)))

(defmethod invert-element :default
  [semigroup x]

  (first (inverse-elements semigroup x)))

; Get the unit elements of a commutative semigroup
(defn unit-element?
  ([semigroup x]
   (not (empty? (inverse-elements semigroup x))))
  ([semigroup identity-element x]
   (unit-element? semigroup x)))

(defmulti unit-elements type)

(defmethod unit-elements :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [commutative-semigroup]

  (let [identities (identity-elements commutative-semigroup)]
    (if (empty? identities)
      #{}
      (naturally-strongly-connected-component-of commutative-semigroup (first identities)))))

(defmethod unit-elements :default
  [semigroup elem]

  (set
    (filter
      (fn [i]
        (unit-element? semigroup i))
      (morphisms semigroup))))

; Idempotent elements
(defn idempotent-element?
  [semigroup i]

  (= i (semigroup (list i i))))

(defn idempotents
  [semigroup]

  (set
    (filter
      (fn [i]
        (idempotent-element? semigroup i))
      (underlying-set semigroup))))

; Computations with the join and meet semilattices of lattices
(defn join-semilattice
  [lattice]

  (->CommutativeSemigroup
    (underlying-set lattice)
    (underlying-relation lattice)
    (fn [[a b]]
      (join-elements lattice a b))))

(defn meet-semilattice
  [lattice]

  (->CommutativeSemigroup
    (underlying-set lattice)
    (transpose (underlying-relation lattice))
    (fn [[a b]]
      (meet-elements lattice a b))))

; We need some way to keep tracking of the size of a semigroup
(defn semigroup-size
  [semigroup]

  (count (underlying-set semigroup)))

; Constructors for special types of commutative semigroups
(defn null-semigroup
  [n]

  (CommutativeSemigroup.
    (->Upto n)
    (fn [[a b]]
      (or (= a b) (zero? b)))
    (fn [[a b]]
      0)))

; A constructor for a basic class of commutative aperiodic semigroups
(defn height-two-tree-ordered-semigroup
  [n m]

  (CommutativeSemigroup.
    (->Upto (inc (+ n m)))
    (fn [[a b]]
      (or
        (= a b)
        (= b 0)))
    (fn [[a b]]
      (if (= a b)
        (if (<= b n)
          b
          0)
        0))))

; Monogenic semigroups
(defn monogenic-simplification
  [index period n]

  (let [initial-segment-size index]
    (if (< n initial-segment-size)
      n
      (let [adjusted-index (- n initial-segment-size)
            period-remainder (mod adjusted-index period)]
        (+ initial-segment-size period-remainder)))))

(defn monogenic-semigroup
  [index period]

  (CommutativeSemigroup.
    (->RangeSet 1 (+ index period))
    (fn [[a b]]
      (or
        (<= a b)
        (and
          (<= index a)
          (<= index b))))
    (fn [[a b]]
      (monogenic-simplification index period (+ a b)))))

; Adjoined elements are those that do not appear anywhere else in the semigroup
(defn adjoined-element?
  [semigroup x]

  (let [remaining-elements (disj (morphisms semigroup) x)]
    (every?
      (fn [[a b]]
        (not= x (semigroup (list a b))))
      (cartesian-power remaining-elements 2))))

; Products in the category of commutative semigroups
(defmethod product CommutativeSemigroup
  [& commutative-semigroups]

  (CommutativeSemigroup.
    (apply cartesian-product (map morphisms commutative-semigroups))
    (apply product-relation (map natural-preorder commutative-semigroups))
    (fn [coll1 coll2]
      (map
        (fn [i]
          ((nth commutative-semigroups i) (list (nth coll1 i) (nth coll2 i))))
        (range (count coll1))))))

; Ontology of commutative semigroups
(defmulti commutative-semigroup? type)

(defmethod commutative-semigroup? :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [commutative-semigroup] true)

(defmethod commutative-semigroup? :default
  [obj] false)

; Ontology of commutative monoids
(defmulti commutative-monoid? type)

(defmethod commutative-monoid? :locus.set.copresheaf.structure.core.protocols/commutative-monoid
  [commutative-monoid] true)

(defmethod commutative-monoid? :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [commutative-semigroup]

  (not (empty? (identity-elements commutative-semigroup))))

; Ontology of commutative groups with zero
(defmulti commutative-group-with-zero? type)

(defmethod commutative-group-with-zero? :locus.set.copresheaf.structure.core.protocols/commutative-group-with-zero
  [obj] true)

(defmethod commutative-group-with-zero? :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [obj]

  (and
    (not (empty? (identity-elements obj)))
    (not (empty? (zero-elements obj)))
    (= (count (unit-elements obj)) (dec (semigroup-size obj)))))

; Ontology of commutative groups
(defmulti commutative-group? type)

(defmethod commutative-group? :locus.set.copresheaf.structure.core.protocols/commutative-group
  [commutative-group] true)

(defmethod commutative-group? :locus.set.copresheaf.structure.core.protocols/commutative-semigroup
  [commutative-group]

  (and
    (commutative-semigroup? commutative-group)
    (not (empty? (identity-elements commutative-group)))
    (let [identity-element (identity-elements commutative-group)]
      (every?
        (fn [i]
          (not (empty? (pairwise-algebraic-divisors commutative-group i identity-element))))
        (morphisms commutative-group)))))

; Semilattices including the join and meet semilattices of lattices are idempotent commutative
; semigroups. To check if a commutative semigroup is a semilattice, check if each element
; is idempotent. Semilattices can be produced from any commutative semigroup using the
; method of semilattice decompositions.
(defn semilattice?
  [obj]

  (and
    (commutative-semigroup? obj)
    (every?
      (fn [i]
        (idempotent-element? obj i))
      (underlying-set obj))))

; Null semigroups are commutative semigroups in which all compositions are equal.
(defn null-semigroup?
  [semigroup]

  (equal-seq?
    (map semigroup (cartesian-power (morphisms semigroup) 2))))

; Test for zero elements in commutative semigroups and monoids
(defn commutative-semigroup-with-zero?
  [semigroup]

  (and
    (commutative-semigroup? semigroup)
    (not (empty? (zero-elements semigroup)))))

(defn commutative-monoid-with-zero?
  [semigroup]

  (and
    (commutative-monoid? semigroup)
    (not (empty? (zero-elements semigroup)))))

; Skeletal commutative monoids are skeletal as categories and have no extra isomorphisms
(defn skeletal-commutative-monoid?
  [monoid]

  (and
    (commutative-monoid? monoid)
    (= (count (unit-elements monoid)) 1)))

; Unipotent commutative semigroups
(defn commutative-unipotent-semigroup?
  [obj]

  (and
    (commutative-semigroup? obj)
    (= (count (idempotents obj)) 1)))

(defn commutative-unipotent-monoid?
  [obj]

  (and
    (commutative-monoid? obj)
    (= (count (idempotents obj)) 1)))

; Conditions on the natural preorders of commutative semigroups and monoids
(defn commutative-jtrivial-semigroup?
  [obj]

  (and
    (commutative-semigroup? obj)
    (antisymmetric? (enumerate-natural-preorder obj))))

(defn commutative-jtrivial-monoid?
  [obj]

  (and
    (commutative-monoid? obj)
    (antisymmetric? (enumerate-natural-preorder obj))))

(defn totally-preordered-commutative-semigroup?
  [obj]

  (and
    (commutative-semigroup? obj)
    (anticoreflexive? (enumerate-natural-preorder obj))))

(defn totally-preordered-commutative-monoid?
  [obj]

  (and
    (commutative-monoid? obj)
    (anticoreflexive? (enumerate-natural-preorder obj))))

(defn totally-ordered-commutative-semigroup?
  [obj]

  (and
    (commutative-semigroup? obj)
    (total-order? (enumerate-natural-preorder obj))))

(defn totally-ordered-commutative-monoid?
  [obj]

  (and
    (commutative-monoid? obj)
    (total-order? (enumerate-natural-preorder obj))))

(defn height-two-tree-ordered-semigroup?
  [semigroup]

  (and
    (commutative-semigroup? semigroup)
    (let [rel (enumerate-natural-preorder semigroup)]
      (and
        (antisymmetric? rel)
        (height-two? rel)))))

(defn total-order-semilattice?
  [semigroup]

  (and
    (semilattice? semigroup)
    (total-order? (enumerate-natural-preorder semigroup))))

(defn height-two-semilattice?
  [semigroup]

  (and
    (semilattice? semigroup)
    (height-two? (enumerate-natural-preorder semigroup))))

; Commutative semigroups with adjoined zero elements
(defn commutative-semigroup-with-adjoined-zero?
  [semigroup]

  (and
    (commutative-semigroup? semigroup)
    (let [zeros (zero-elements semigroup)]
      (and
        (not (empty? zeros))
        (let [zero-element (first zeros)]
          (adjoined-element? semigroup zero-element))))))

(defn commutative-monoid-with-adjoined-zero?
  [semigroup]

  (and
    (commutative-semigroup-with-adjoined-zero? semigroup)
    (not (empty? (identity-elements semigroup)))))

