(ns locus.algebra.semigroup.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all])
  (:import (locus.order.lattice.core.object Lattice)
           (java.util Optional)
           (locus.set.mapping.general.core.object SetFunction)
           (locus.algebra.commutative.semigroup.object CommutativeSemigroup)))

; A semigroup is simply a semigroupoid with a single object. We further define
; semigroups to be structured sets by defining a functor to Sets as well
; as structured functions by defining a functor to Sets^(->). The functor
; to Sets^(->) maps a semigroup to its composition function.
(deftype Semigroup [elems op]
  ; Semigroups are structured sets
  ConcreteObject
  (underlying-set [this] elems)

  ; Semigroups are structured quivers
  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ; Semigroups are structured functions
  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Semigroup :locus.set.copresheaf.structure.core.protocols/semigroup)

; To semigroup conversion
(defmulti to-semigroup type)

(defmethod to-semigroup SetFunction
  [func]

  (Semigroup. (outputs func) func))

(defmethod to-semigroup CommutativeSemigroup
  [^CommutativeSemigroup semigroup]

  (->Semigroup (.-elems semigroup) (.-op semigroup)))

(defmethod to-semigroup Semigroup
  [semigroup] semigroup)

; Noncommutative theory of zero elements
(defn right-zero-element?
  [semigroup z]

  (every?
    (fn [x]
      (= (semigroup (list x z)) z))
    (morphisms semigroup)))

(defn left-zero-element?
  [semigroup z]

  (every?
    (fn [x]
      (= (semigroup (list z x)) z))
    (morphisms semigroup)))

; Noncommutative theory of identity elements
(defn right-identity-element?
  [semigroup e]

  (every?
    (fn [x]
      (= (semigroup (list x e)) x))
    (morphisms semigroup)))

(defn left-identity-element?
  [semigroup e]

  (every?
    (fn [x]
      (= (semigroup (list e x)) x))
    (morphisms semigroup)))

; Central elements
(defn central-element?
  [semigroup elem]

  (every?
    (fn [i]
      (= (semigroup (list i elem))
         (semigroup (list elem i))))
    (underlying-set semigroup)))

(defn center
  [semigroup]

  (set
    (filter
      (fn [i]
        (central-element? semigroup i))
      (underlying-set semigroup))))

(defn commuting-clique?
  [semigroup coll]

  (every?
    (fn [pair]
      (let [[a b] (seq pair)]
        (= (semigroup (list a b))
           (semigroup (list b a)))))
    (selections coll 2)))

; Get the commuting graph of a semigroup
(defn com
  [semigroup]

  (union
    (unary-family (underlying-set semigroup))
    (set
      (filter
        (fn [pair]
          (let [[a b] (seq pair)]
            (= (semigroup (list a b))
               (semigroup (list b a)))))
        (selections (underlying-set semigroup) 2)))))

(defn commutativity-preorder
  [semigroup]

  (logical-preorder
    (fn [x]
      (set
        (filter
          (fn [y]
            (= (semigroup (list x y))
               (semigroup (list y x))))
          (underlying-set semigroup))))
    (underlying-set semigroup)))

(def maximal-commuting-cliques
  (comp maximal-cliques com))

; Centralizers
(defn element-centralizer
  [semigroup x]

  (set
    (filter
      (fn [i]
        (= (semigroup (list i x))
           (semigroup (list x i))))
      (underlying-set semigroup))))

(defn set-centralizer
  [semigroup coll]

  (set
    (filter
      (fn [i]
        (every?
          (fn [x]
            (= (semigroup (list i x))
               (semigroup (list x i))))
          coll))
      (underlying-set semigroup))))

(defn commuting-degree
  [semigroup x]

  (count (element-centralizer semigroup x)))

(defn commutative-principal-filter
  [semigroup x]

  (principal-filter (commutativity-preorder semigroup) x))

(defn commutativity-principal-filters
  [semigroup]

  (principal-filters (commutativity-preorder semigroup)))

; Compute the inverses of elements of a semigroup
(defn find-element-inverses
  [semigroup identity-element elem]

  (filter
    (fn [i]
      (= identity-element
         (semigroup (list i elem))
         (semigroup (list elem i))))
    (underlying-set semigroup)))

(defmethod inverse-elements :default
  [semigroup elem]

  (let [identities (identity-elements semigroup)]
    (if (empty? identities)
      '()
      (let [identity-element (first identities)]
        (find-element-inverses semigroup identity-element elem)))))

(defmethod invert-element :default
  [semigroup x]

  (first (find-element-inverses semigroup (identity-element semigroup) x)))

; Inverses and pseudoinverses are distinguished from inverses in the sense of
; a monoid by the fact that they emerge from semigroup theory.
(defn regular-pair?
  [semigroup a x]

  (= a (apply-semigroup semigroup [a x a])))

(defn pseudoinverses
  [semigroup elem]

  (set
    (filter
      (fn [morphism]
        (regular-pair? semigroup elem morphism))
      (morphisms semigroup))))

(defn generalized-inverse-pair?
  [semigroup elem inverse]

  (and
    (= elem (apply-semigroup semigroup [elem inverse elem]))
    (= inverse (apply-semigroup semigroup [inverse elem inverse]))))

(defn generalized-inverses
  [semigroup elem]

  (set
    (filter
      (fn [morphism]
        (generalized-inverse-pair? semigroup elem morphism))
      (morphisms semigroup))))

; Sandwhich sets of regular semigroups
(defn sandwhich-set
  [semigroup e f]

  (let [inverses (generalized-inverses semigroup (semigroup (list e f)))]
    (set
      (filter
        (fn [g]
          ; check for idempotence
          (= (semigroup (list g g)) g)

          ; the sandwhich condition
          (= (semigroup (list g e))
             (semigroup (list f g))
             g))
        inverses))))

; Get the dual of a semigroup
(defmethod dual :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup]

  (Semigroup.
    (underlying-set semigroup)
    (fn [pair]
      (semigroup (reverse pair)))))

; Products of semigroups
(defn semigroup-product-function
  [& semigroups]

  (fn [[coll1 coll2]]
    (map
      (fn [i]
        ((nth semigroups i) (list (nth coll1 i) (nth coll2 i))))
      (range (count coll1)))))

(defn semigroup-product
  [& semigroups]

  (Semigroup.
    (apply cartesian-product (map underlying-set semigroups))
    (apply semigroup-product-function semigroups)))

(defmethod product :locus.set.copresheaf.structure.core.protocols/semigroup
  [& args]

  (apply semigroup-product args))

; Subalgebra lattices of semigroups
(defn subsemigroup?
  [semigroup subset]

  (letfn [(contains?* [coll x]
            (not
              (every?
                (fn [i]
                  (not= i x))
                coll)))]
    (every?
      (fn [pair]
        (contains?* subset (semigroup pair)))
      (cartesian-power subset 2))))

(defn all-subsemigroups
  [semigroup]

  (set
    (filter
      (partial subsemigroup? semigroup)
      (power-set (underlying-set semigroup)))))

(defn identity-preserving-subsemigroup?
  [semigroup coll]

  (and
    (subsemigroup? semigroup coll)
    (superset? (list (identity-elements semigroup) coll))))

(defn identity-preserving-subsemigroups
  [monoid]

  (set
    (filter
      (partial subsemigroup? monoid)
      (logical-interval (identity-elements monoid) (underlying-set monoid)))))

(defn zero-preserving-subsemigroups
  [semigroup]

  (let [zeros (zero-elements semigroup)]
    (if (empty? zeros)
      #{}
      (set
        (filter
          (partial subsemigroup? semigroup)
          (logical-interval zeros (underlying-set semigroup)))))))

(defn subsemigroup-closure
  [semigroup coll]

  (letfn [(get-all-composites [semigroup coll]
            (map
              semigroup
              (cartesian-power coll 2)))]
    (loop [current-elements (set coll)]
      (let [next-elements (get-all-composites semigroup current-elements)]
        (if (every?
              (fn [i]
                (contains? current-elements i))
              next-elements)
          current-elements
          (recur (union current-elements (set next-elements))))))))

(defmethod sub :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup]

  (Lattice.
    (set
      (filter
        (partial subsemigroup? semigroup)
        (power-set (underlying-set semigroup))))
    (comp (partial subsemigroup-closure semigroup) union)
    intersection))

(defn restrict-semigroup
  [semigroup, coll]

  (Semigroup.
    coll
    (.op semigroup)))

; Congruences of semigroups
(defn semigroup-congruence?
  [semigroup partition]

  (every?
    (fn [[coll1 coll2]]
      (equal-seq?
        (map
          (comp (partial projection partition) semigroup)
          (cartesian-product coll1 coll2))))
    (cartesian-power partition 2)))

(defn enumerate-semigroup-congruences
  [semigroup]

  (filter
    (fn [partition]
      (semigroup-congruence? semigroup partition))
    (set-partitions (set (underlying-set semigroup)))))

(defmethod con :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup]

  (Lattice.
    (->SeqableUniversal
      (fn [partition]
        (semigroup-congruence? semigroup partition))
      (enumerate-semigroup-congruences semigroup)
      {})
    join-set-partitions
    meet-set-partitions))

(defn quotient-semigroup
  [semigroup partition]

  (Semigroup.
    partition
    (fn [[c1 c2]]
      (projection partition (semigroup (list (first c1) (first c2)))))))

; Commutative subsemigroups
(defn commutative-subsemigroups
  [semigroup]

  (set
    (filter
      (fn [coll]
        (subsemigroup? semigroup coll))
      (cl subclass-closed? (com semigroup)))))

; Construction of composition semigroups of categories and semigroupoids
; This is part of the semigroup theoretic methods of category theory
(defn composition-semigroup
  [semigroupoid]

  (Semigroup.
    (cartesian-coproduct #{0} (morphisms semigroupoid))
    (fn [[[i v] [j w]]]
      (cond
        (zero? i) (list 0 0)
        (zero? j) (list 0 0)
        :else (if (composable-elements? semigroupoid v w)
                (list 1 (semigroupoid (list v w)))
                (list 0 0))))))

; Display the multiplication table of semigroup
(defn multiplication-table
  [semigroup]

  (let [elems (vec (seq (morphisms semigroup)))
        indices (range (count elems))]
    (vec
      (map
        (fn [i]
          (vec
            (map
              (fn [j]
                (.indexOf
                  elems
                  (semigroup (list (nth elems i) (nth elems j)))))
              indices)))
        indices))))

; Constructors for common classes of semigroups
(defn left-zero-semigroup
  [n]

  (Semigroup.
    (->Upto n)
    (fn [[a b]] a)))

(defn right-zero-semigroup
  [n]

  (Semigroup.
    (->Upto n)
    (fn [[a b]] b)))

(defn rectangular-band
  [n m]

  (cond
    (= n 1) (right-zero-semigroup m)
    (= m 1) (left-zero-semigroup n)
    :else (product (left-zero-semigroup n)
                   (right-zero-semigroup m))))

; We need to be able to create the nth complete brandt semigroup
(defn nth-complete-brandt-semigroup
  [n]

  (Semigroup.
    (set
      (cons '() (cartesian-power (set (range n)) 2)))
    (fn [[a b]]
      (if (or (empty? a)
              (empty? b))
        '()
        (let [[a1 a2] a
              [b1 b2] b]
          (if (= b2 a1)
            (list b1 a2)
            '()))))))

(defn edges-semigroup
  [rel]

  (Semigroup.
    (union rel #{'()})
    (fn [[p1 p2]]
      (if (or (empty? p1) (empty? p2))
        '()
        (let [[a b] p1
              [c d] p2]
          (if (= d a)
            (list c b)
            '()))))))

; Semigroup of relations
(defn semigroup-of-relations
  [coll]

  (Semigroup.
    (->PowerSet (->CompleteRelation coll))
    (fn [[rel1 rel2]]
      (compose-relations rel1 rel2))))

; Power semigroup and monoid
(defn compose-subsets
  [semigroup s1 s2]

  (set-image semigroup (product s1 s2)))

(defn power-semigroup
  [semigroup]

  (Semigroup.
    (->PowerSet (underlying-set semigroup))
    (fn [[coll1 coll2]] (compose-subsets semigroup coll1 coll2))))

; Fundamental examples
(def r2
  (right-zero-semigroup 2))

(def l2
  (left-zero-semigroup 2))

(def z2
  (null-semigroup 2))

(def c2
  (monogenic-semigroup 1 2))

; Greens relations of semigroups
(defn principal-left-ideal
  [semigroup x]

  (conj
    (set
      (map
        (fn [i]
          (semigroup (list i x)))
        (underlying-set semigroup)))
    x))

(defn principal-right-ideal
  [semigroup x]

  (conj
    (set
      (map
        (fn [i]
          (semigroup (list x i)))
        (underlying-set semigroup)))
    x))

(defn principal-two-sided-ideal
  [semigroup x]

  (conj
    (set
      (map
        (fn [[l r]]
          (semigroup (list (semigroup (list l x)) r)))
        (let [coll (underlying-set semigroup)]
          (product coll coll))))
    x))

(defn lpreorder
  [semigroup]

  (transpose
    (logical-preorder
      (fn [i]
        (principal-left-ideal semigroup i))
      (morphisms semigroup))))

(defn rpreorder
  [semigroup]

  (transpose
    (logical-preorder
      (fn [i]
        (principal-right-ideal semigroup i))
      (morphisms semigroup))))

(defn jpreorder
  [semigroup]

  (transpose
    (logical-preorder
      (fn [i]
        (principal-two-sided-ideal semigroup i))
      (morphisms semigroup))))

(defn lrelation
  [semigroup]

  (pn (fn [a b]
        (= (principal-left-ideal semigroup a)
           (principal-left-ideal semigroup b)))
      (morphisms semigroup)))

(defn rrelation
  [semigroup]

  (pn (fn [a b]
        (= (principal-right-ideal semigroup a)
           (principal-right-ideal semigroup b)))
      (morphisms semigroup)))

(defn jrelation
  [semigroup]

  (pn (fn [a b]
        (= (principal-two-sided-ideal semigroup a)
           (principal-two-sided-ideal semigroup b)))
      (morphisms semigroup)))

(defn hrelation
  [semigroup]

  (meet-set-partitions (lrelation semigroup) (rrelation semigroup)))

(defn drelation
  [semigroup]

  (join-set-partitions (lrelation semigroup) (rrelation semigroup)))

; Fallback on the Green's J preorder when a natural preordering is not inherently defined
(defmethod natural-preorder :default
  [semigroup]

  (jpreorder semigroup))

; Ideal families
(defn two-sided-ideals
  [semigroup]

  (filters (jpreorder semigroup)))

(defn left-ideals
  [semigroup]

  (filters (lpreorder semigroup)))

(defn right-ideals
  [semigroup]

  (filters (rpreorder semigroup)))

(defn left-ideal?
  [semigroup coll]

  (every?
    (fn [[semigroup-element ideal-element]]
      (contains? coll (semigroup (list semigroup-element ideal-element))))
    (cartesian-product (underlying-set semigroup) coll)))

(defn right-ideal?
  [semigroup coll]

  (every?
    (fn [[semigroup-element ideal-element]]
      (contains? coll (semigroup (list ideal-element semigroup-element))))
    (cartesian-product (underlying-set semigroup) coll)))

(defn two-sided-ideal?
  [semigroup coll]

  (every?
    (fn [[semigroup-element ideal-element]]
      (and
        (contains? coll (semigroup (list ideal-element semigroup-element)))
        (contains? coll (semigroup (list semigroup-element ideal-element)))))
    (cartesian-product (underlying-set semigroup) coll)))

; The Rees factors of ideals of a semigroup
(defn rees-semigroup-congruence
  [semigroup ideal]

  (let [remaining-elements (difference (underlying-set semigroup) ideal)]
    (conj (unary-family remaining-elements) ideal)))

(defn rees-factor-semigroup
  [semigroup ideal]

  (quotient-semigroup
    semigroup
    (rees-semigroup-congruence semigroup ideal)))

; The zero divisor graph of semigroup theory provides a fundamental
; interface to the idea of composition semigroups of semigroupoids.
(defn zero-divisor-graph
  [semigroup]

  (let [zeros (zero-elements semigroup)]
    (if (empty? zeros)
      #{}
      (let [z (first zeros)]
        (set
          (filter
            (fn [pair]
              (= (semigroup pair) z))
            (cartesian-power (underlying-set semigroup) 2)))))))

; Let S be a semigroup then we can always adjoin a zero to the semigroups to that the zero
; element is greater than all other elements in the Green's J preorder.
(defmethod adjoin-zero :default
  [semigroup]

  (Semigroup.
    (cartesian-coproduct #{0} (underlying-set semigroup))
    (fn [[[i v] [j w]]]
      (cond
        (zero? i) (list 0 0)
        (zero? j) (list 0 0)
        :else (list 1 (semigroup (list v w)))))))

; The spectrum of a semigroup
(defn prime-subsemigroup?
  [semigroup coll]

  (and
    (subsemigroup? semigroup coll)
    (subsemigroup? semigroup (difference (underlying-set semigroup) coll))))

(defn semigroup-prime-ideal?
  [semigroup coll]

  (and
    (two-sided-ideal? semigroup coll)
    (subsemigroup? semigroup (difference (underlying-set semigroup) coll))))

(defn semigroup-spectrum
  [semigroup]

  (set
    (filter
      (fn [coll]
        (subsemigroup? semigroup (difference (underlying-set semigroup) coll)))
      (two-sided-ideals semigroup))))

; Get the principal subsemigroup
(defn semigroup-element-iterates
  [semigroup starting-element]

  (loop [current-element starting-element
         seen-elements #{}]
    (if (contains? seen-elements current-element)
      seen-elements
      (recur
        (semigroup (list current-element starting-element))
        (conj seen-elements current-element)))))

; Nilpotent elements
(defn nilpotent-element?
  [semigroup elem]

  (let [z (first (zero-elements semigroup))]
    (and
      (not (nil? z))
      (contains? (semigroup-element-iterates semigroup elem) z))))

(defn nilpotent-elements
  [semigroup]

  (let [z (first (zero-elements semigroup))]
    (when (not (nil? z))
      (set
        (filter
          (fn [i]
            (contains? (semigroup-element-iterates semigroup i) z))
          (underlying-set semigroup))))))

; The iteration preorder of a semigroup
(defn iteration-preorder
  [semigroup]

  (transpose
    (logical-preorder
      (fn [elem]
        (semigroup-element-iterates semigroup elem))
      (underlying-set semigroup))))

(defn semigroup-element-roots
  [semigroup elem]

  (set
    (filter
      (fn [i]
        (contains? (semigroup-element-iterates semigroup i) elem))
      (underlying-set semigroup))))

(defn radical-subsemigroup?
  [semigroup coll]

  (let [rel (iteration-preorder semigroup)]
    (and
      (subsemigroup? semigroup coll)
      (ideal-vertex-set? rel coll))))

(defn semigroup-radical-ideal?
  [semigroup coll]

  (let [rel (iteration-preorder semigroup)]
    (and
      (two-sided-ideal? semigroup coll)
      (ideal-vertex-set? rel coll))))

(defn semigroup-radical-ideals
  [semigroup]

  (let [rel (iteration-preorder semigroup)]
    (filter
      (fn [i]
        (ideal-vertex-set? rel i))
      (two-sided-ideals semigroup))))

; Create a semigroup by a table
(defn semigroup-by-table
  [coll]

  (let [n (count coll)]
    (Semigroup.
      (->Upto n)
      (fn [[i j]]
        (nth (nth coll i) j)))))

; Classification of semigroups
(derive Semigroup :locus.set.copresheaf.structure.core.protocols/semigroup)

(defmulti semigroup? type)

(defmethod semigroup? :locus.set.copresheaf.structure.core.protocols/semigroup
  [x] true)

(defmethod semigroup? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [x] (= (count (objects x)) 1))

(defmethod semigroup? :default
  [x] false)

; Classification of monoids
(defmulti intrinsic-monoid? type)

(defmethod intrinsic-monoid? :locus.set.copresheaf.structure.core.protocols/monoid
  [x] true)

(defmethod intrinsic-monoid? :default
  [x] false)

(defmulti monoid? type)

(defmethod monoid? :locus.set.copresheaf.structure.core.protocols/monoid
  [x] true)

(defmethod monoid? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [x]

  (and
    (= (count (objects x)) 1)
    (not (empty? (identity-elements x)))))

(defmethod monoid? :default
  [x] false)

(defmethod category? :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup] (not (empty? (identity-elements semigroup))))

; Special classes of semigroups and monoids
(defn skeletal-monoid?
  [monoid]

  (and
    (monoid? monoid)
    (= (count (unit-elements monoid)) 1)))

(defn band?
  [structure]

  (and
    (semigroup? structure)
    (every?
      (fn [i]
        (= (structure (list i i)) i))
      (underlying-set structure))))

(defn unital-band?
  [structure]

  (and
    (monoid? structure)
    (band? structure)))

; Generalisations of commutativity on the set of idempotents
(defn idempotent-commutative-semigroup?
  [semigroup]

  (commuting-clique? semigroup (idempotents semigroup)))

(defn idempotent-central-semigroup?
  [semigroup]

  (every?
    (fn [idempotent]
      (central-element? semigroup idempotent))
    (idempotents semigroup)))

; Special types of rectangular bands
(defn rectangular-band?
  [structure]

  (and
    (semigroup? structure)
    (every?
      (fn [pair]
        (not= (structure pair)
              (structure (reverse pair))))
      (cartesian-power (underlying-set structure) 2))))

(defn left-zero-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (every?
      (fn [[x y]]
        (= (semigroup (list x y)) x))
      (cartesian-power (underlying-set semigroup) 2))))

(defn right-zero-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (every?
      (fn [[x y]]
        (= (semigroup (list x y)) y))
      (cartesian-power (underlying-set semigroup) 2))))

; Test for groups
(defmulti intrinsic-group? type)

(defmethod intrinsic-group? :locus.set.copresheaf.structure.core.protocols/group
  [x] true)

(defmethod intrinsic-group? :default
  [obj] false)

(defmulti group? type)

(defmethod group? :locus.set.copresheaf.structure.core.protocols/group
  [x] true)

(defmethod group? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [obj]

  (and
    (semigroup? obj)
    (let [identities (identity-elements obj)]
      (and
        (not (empty? identities))
        (let [identity (first identities)]
          (every?
            (fn [elem]
              (unit-element? obj identity elem))
            (underlying-set obj)))))))

(defmethod group? :default
  [x] false)

; Semigroups with zero
(defn semigroup-with-zero?
  [semigroup]

  (and
    (semigroup? semigroup)
    (not (empty? (zero-elements semigroup)))))

(def monoid-with-zero?
  (intersection
    semigroup-with-zero?
    monoid?))

(defmulti group-with-zero? type)

(defmethod group-with-zero? :locus.set.copresheaf.structure.core.protocols/group-with-zero
  [group-with-zero] true)

(defmethod group-with-zero? :default
  [semigroup]

  (and
    (semigroup-with-zero? semigroup)
    (group?
      (restrict-semigroup
        semigroup
        (difference
          (set (morphisms semigroup))
          (zero-elements semigroup))))))

; Checks for commutativity
(defmethod commutative-semigroup? :default
  [semigroup]

  (and
    (semigroup? semigroup)
    (commuting-clique? semigroup (morphisms semigroup))))

(defmethod commutative-monoid? :default
  [semigroup]

  (and
    (monoid? semigroup)
    (commuting-clique? semigroup (morphisms semigroup))))

(defmethod commutative-group? :default
  [semigroup]

  (and
    (group? semigroup)
    (commuting-clique? semigroup (morphisms semigroup))))

(defmethod commutative-group-with-zero? :default
  [semigroup]

  (and
    (group-with-zero? semigroup)
    (commuting-clique? semigroup (morphisms semigroup))))

; Special classes of semigroups
(defn jtrivial?
  [semigroup]

  (and
    (semigroup? semigroup)
    (unary-family? (jrelation semigroup))))

(defn ltrivial?
  [semigroup]

  (unary-family? (lrelation semigroup)))

(defn rtrivial?
  [semigroup]

  (unary-family? (rrelation semigroup)))

(defn htrivial?
  [semigroup]

  (unary-family? (hrelation semigroup)))

(defn jtotal?
  [semigroup]

  (and
    (semigroup? semigroup)
    (unique-family? (jrelation semigroup))))

(defn ltotal?
  [semigroup]

  (and
    (semigroup? semigroup)
    (unique-family? (lrelation semigroup))))

(defn rtotal?
  [semigroup]

  (and
    (semigroup? semigroup)
    (unique-family? (rrelation semigroup))))

; Test for condensible semigroups
(defn condensible-semigroup?
  [semigroup]

  (semigroup-congruence? semigroup (jrelation semigroup)))

(defn semigroup-condensation
  [semigroup]

  (quotient-semigroup semigroup (jrelation semigroup)))

(defn commutative-condensation?
  [semigroup]

  (and
    (condensible-semigroup? semigroup)
    (commutative-semigroup? (semigroup-condensation semigroup))))

; The special class of E-semigroups consists of all semigroups
; whose idempotents form a subsemigroup
(defn e-semigroup?
  [semigroup]

  (subsemigroup? semigroup (idempotents semigroup)))

(defn semigroup-with-adjoined-zero?
  [semigroup]

  (and
    (semigroup? semigroup)
    (let [zeros (zero-elements semigroup)]
      (and
        (not (empty? zeros))
        (let [zero-element (first zeros)]
          (adjoined-element? semigroup zero-element))))))

(def monoid-with-adjoined-zero?
  (intersection
    semigroup-with-adjoined-zero?
    monoid?))

; Zero simple semigroups are used in the Rees quotient factor theory of semigroups
(defn zero-simple-semigroup?
  [semigroup]

  (and
    (semigroup-with-zero? semigroup)
    (= (count (jrelation semigroup)) 2)))

; Regular semigroups
(defn regular-element?
  [semigroup x]

  (not
    (every?
      (fn [y]
        (not (regular-pair? semigroup x y)))
      (morphisms semigroup))))

(defn regular-elements
  [semigroup]

  (set
    (filter
      (fn [i]
        (regular-element? semigroup i))
      (morphisms semigroup))))

(defn regular-semigroup?
  [semigroup]

  (every?
    (fn [elem]
      (regular-element? semigroup elem))
    (morphisms semigroup)))

(def orthodox-semigroup?
  (intersection
    regular-semigroup?
    e-semigroup?))

(def simple-orthodox-semigroup?
  (intersection
    orthodox-semigroup?
    jtotal?))

(def inverse-semigroup?
  (intersection
    regular-semigroup?
    idempotent-commutative-semigroup?))

(def clifford-semigroup?
  (intersection
    regular-semigroup?
    idempotent-central-semigroup?))

(def brandt-semigroup?
  (intersection
    zero-simple-semigroup?
    inverse-semigroup?))

(defn completely-regular-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (every?
      (fn [hclass]
        (group? (restrict-semigroup semigroup hclass)))
      (hrelation semigroup))))

(defn group-symmetric?
  [semigroup]

  (and
    (semigroup? semigroup)
    (every?
      (fn [coll]
        (or (= (count coll) 1)
            (group? (restrict-semigroup semigroup coll))))
      (hrelation semigroup))))

(defn divisibility-commutative-semigroup?
  [semigroup]

  (= (rrelation semigroup)
     (lrelation semigroup)))

(defn commutative-condensation-divisibility-commutative-semigroup?
  [semigroup]

  (and
    (= (rrelation semigroup) (lrelation semigroup))
    (commutative-semigroup? (semigroup-condensation semigroup))))

; Commutative clifford semigroups
(def commutative-clifford-semigroup?
  (intersection
    regular-semigroup?
    commutative-semigroup?))

; Monogenic semigroups
(defn monogenic-semigroup?
  [semigroup]

  (not
    (every?
      (fn [i]
        (not
          (equal-universals?
            (underlying-set semigroup)
            (semigroup-element-iterates semigroup i))))
      (underlying-set semigroup))))

(def cyclic-group?
  (intersection
    group?
    monogenic-semigroup?))

; Nilpotent semigroups theory
(defn nilpotent-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (every?
      (fn [i]
        (nilpotent-element? semigroup i))
      (underlying-set semigroup))))

(defn nilpotent-commutative-semigroup?
  [semigroup]

  (and
    (nilpotent-semigroup? semigroup)
    (commutative-semigroup? semigroup)))

; Reduced semigroups with zero have no non-trivial nilpotents
(defn reduced-semigroup-with-zero?
  [semigroup]

  (and
    (semigroup-with-zero? semigroup)
    (<= (count (nilpotent-elements semigroup)) 1)))

(defn reduced-commutative-semigroup-with-zero?
  [semigroup]

  (and
    (commutative-semigroup-with-zero? semigroup)
    (<= (count (nilpotent-elements semigroup)) 1)))

; Subtotal bands are precisely the semigroups in which all subsets are subsemigroups
(defn subtotal-band?
  [semigroup]

  (and
    (semigroup? semigroup)
    (every?
      (fn [coll]
        (subsemigroup? semigroup coll))
      (power-set (underlying-set semigroup)))))

; Classification of semigroups by their ordering relations
(defn totally-ordered-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (jtrivial? semigroup)
    (total-order? (jpreorder semigroup))))

(defn totally-preordered-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (total-preorder? (jpreorder semigroup))))

(defn totally-ordered-monoid?
  [semigroup]

  (and
    (monoid? semigroup)
    (total-order? (jpreorder semigroup))))

(defn totally-preordered-monoid?
  [semigroup]

  (and
    (monoid? semigroup)
    (total-preorder? (jpreorder semigroup))))

; Special types of semigroups by their idempotents
(defn semiband?
  [semigroup]

  (= (underlying-set semigroup)
     (subsemigroup-closure
       semigroup
       (idempotents semigroup))))

(defn unipotent-semigroup?
  [semigroup]

  (= (count (idempotents semigroup)) 1))

; Congruence free semigroups have no non-trivial congruences
(defn congruence-free-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (<= (count (enumerate-semigroup-congruences semigroup)) 2)))

; Surjective semigroups are those in which each element is produced by some product
(defn surjective-semigroup?
  [semigroup]

  (and
    (semigroup? semigroup)
    (or
      (not (empty? (identity-elements semigroup)))
      (equal-universals?
        (underlying-set semigroup)
        (set
          (map
            semigroup
            (cartesian-power (underlying-set semigroup) 2)))))))

; Locally inverse semigroups
(defn idempotent-wrapper-semigroup
  [semigroup e]

  (restrict-semigroup
    semigroup
    (set
      (map
        (fn [morphism]
          (apply-semigroup semigroup (list e morphism e)))
        (morphisms semigroup)))))

(defn locally-inverse-semigroup?
  [semigroup]

  (every?
    (fn [e]
      (inverse-semigroup? (idempotent-wrapper-semigroup semigroup e)))
    (idempotents semigroup)))