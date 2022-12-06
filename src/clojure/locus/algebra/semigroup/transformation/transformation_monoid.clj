(ns locus.algebra.semigroup.transformation.transformation-monoid
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.effects.global.transformation :refer :all]
            [locus.base.effects.global.permutation :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.category.hom.sethom :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.algebra.semigroup.monoid.end :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import
    (locus.base.function.core.object SetFunction)
    (locus.algebra.semigroup.monoid.morphism MonoidMorphism)
    (locus.base.effects.global.permutation Permutation)
    (locus.base.effects.global.transformation Transformation)))

; Let C be a concrete category with a single object. Then by the fact that the set-valued functor on C
; is faithful, each element of C is uniquely mapped to a distinct function. It follows that C
; is equivalent to a transformation monoid. So in our categorical framework, we define transformation
; monoids to be single object concrete categories.
(deftype TransformationMonoid [elems op id coll action]
  ConcreteObject
  (underlying-set [this] elems)

  ; Transformation monoids are categories and therefore quivers
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

  ; Every semigroup is a function
  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ; Transformation monoids are concrete categories
  ConcreteCategoricalStructure
  (object-to-set [this obj] coll)
  (morphism-to-function [this morphism] (SetFunction. coll coll (fn [x] (action morphism x)))))

; Tagging transformation monoids as semigroupoids
(derive TransformationMonoid :locus.elementary.copresheaf.core.protocols/concrete-monoid)

(defmethod identity-elements TransformationMonoid
  [monoid]

  #{(.id monoid)})

; Transformation monoid
(defmethod to-mset TransformationMonoid
  [monoid]

  (->MSet monoid (.coll monoid) (.action monoid)))

; Transformation semigroup creation methods:
; A number of methods are provided to ease in the creation of transformation monoids
; including a number of conversion functions involving existing structures.
(defn extend-monoid
  [monoid coll action]

  (->TransformationMonoid
    (underlying-set monoid)
    monoid
    (first (identity-elements monoid))
    coll
    action))

(defmulti to-transformation-monoid type)

(defmethod to-transformation-monoid TransformationMonoid
  [monoid] monoid)

(defmethod to-transformation-monoid Transformation
  [transformation]

  (extend-monoid
    (let [[index period] (index-period transformation)] (monogenic-monoid index period))
    (underlying-set transformation)
    (partial iteratively-apply transformation)))

(defmethod to-transformation-monoid Permutation
  [permutation]

  (extend-monoid
    (cyclic-group (permutation-period permutation))
    (underlying-set permutation)
    (partial iteratively-apply permutation)))

(defn as-transformation-monoid
  [transformations coll]

  (TransformationMonoid.
    transformations
    (fn [[a b]] (compose a b))
    (identity-transformation coll)
    coll
    (fn [transformation x] (transformation x))))

; Represent an element as a transformation
(defn transformation-element
  [monoid action]

  (->Transformation
    (.coll monoid)
    (fn [x]
      ((.action monoid) action x))))

; Restrict a transformation monoid
(defn restrict-transformation-monoid
  [^TransformationMonoid monoid, coll]

  (TransformationMonoid.
    coll
    (.op monoid)
    (.id monoid)
    (.coll monoid)
    (.action monoid)))

; Transformation monoids are a special sort of object that can be filtered
(defn filter-transformation-monoid
  [func, ^TransformationMonoid monoid]

  (restrict-transformation-monoid
    monoid
    (filter func (underlying-set monoid))))

; Lens monoid restrictions
(defn lens-monoid-restriction
  [monoid active-partition stable-partition]

  (filter-transformation-monoid
    (fn [i]
      (lens-member-transformation? i active-partition stable-partition))
    monoid))

; Take a transformation monoid and embed it into the endomorphism monoid of a set
(defn transformation-monoid-embedding
  [monoid]

  (MonoidMorphism.
    monoid
    (end (underlying-set monoid))
    (fn [elem]
      (morphism-to-function monoid elem))))

; Seqable transformations
(defn seqable-transformations
  [coll]

  (->SeqableUniversal
    (fn [i]
      (and
        (endofunction? i)
        (equal-universals? (inputs i) coll)))
    (map to-transformation (enumerate-self-mappings coll))
    {:count (bigint (.pow (BigInteger/valueOf (count coll)) (count coll)))}))

(defn full-transformation-monoid
  [coll]

  (as-transformation-monoid
    (seqable-transformations coll)
    coll))

(defn lens-transformation-monoid
  [active-partition stable-partition]

  (lens-monoid-restriction
    (full-transformation-monoid (apply union active-partition))
    active-partition
    stable-partition))

; The semiband of singular maps on a set
(defn sing
  [coll]

  (filter-transformation-monoid
    (fn [transformation]
      (not (invertible? (underlying-function transformation))))
    (full-transformation-monoid coll)))

; The actual crux of the transformation monoid system involves numeric representations
(defn full-numeric-transformation-monoid
  [sorted-coll]

  (extend-monoid
    (let [n (count sorted-coll)]
      (->Monoid
        (seqable-cartesian-power (set (range n)) n)
        (fn [[a b]] (compose-sequences a b n))
        (range n)))
    (set sorted-coll)
    (fn [action x]
      (nth sorted-coll (nth action (.indexOf sorted-coll x))))))

(defn full-numeric-permutation-group
  [sorted-coll]

  (extend-monoid
    (let [n (count sorted-coll)]
      (->Monoid
        (enumerate-permutations (set (range n)))
        (fn [[a b]] (compose-sequences a b n))
        (range n)))
    (set sorted-coll)
    (fn [action x]
      (nth sorted-coll (nth action (.indexOf sorted-coll x))))))

; Convert a relation to an adjacency list form
(defn numericize-relation
  [sorted-coll rel]

  (let [indexing-map (zipmap
                       sorted-coll
                       (range (count sorted-coll)))]
    (set
      (map
        (partial map indexing-map)
        rel))))

(defn enumerate-numeric-preorder-transformations
  [adjacency-list]

  (apply
    seqable-cartesian-product
    (map
      (fn [i]
        (set (adjacency-list i)))
      (range (count (keys adjacency-list))))))

(defn numeric-preorder-monoid
  [adjacency-list]

  (->Monoid
    (enumerate-numeric-preorder-transformations adjacency-list)
    (fn [[a b]] (compose-sequences a b))
    (range (count (keys adjacency-list)))))

(defn increasing-transformations
  [rel]

  (let [sorted-coll (vec (seq (vertices rel)))
        numeric-relation (numericize-relation sorted-coll rel)]
    (extend-monoid
      (numeric-preorder-monoid (to-adjacency-list numeric-relation))
      (set sorted-coll)
      (fn [action x]
        (nth sorted-coll (nth action (.indexOf sorted-coll x)))))))

; Permutations
(defn partition-permutations
  [coll]

  (as-transformation-monoid
    (set
      (map
        (fn [perms]
          (to-permutation (apply merge perms)))
        (apply
          cartesian-product
          (map (comp set enumerate-permutation-maps seq) coll))))
    (apply union coll)))

; Lens transformation monoids and the theory of local actions
(defn numeric-lens-transformation-monoid
  [active-partition stable-partition]

  (let [n (count (apply union active-partition))]
    (as-transformation-monoid
      (set
        (filter
          (fn [i]
            (lens-member-transformation? i active-partition stable-partition))
          (map numeric-transformation (seqable-cartesian-power (set (range n)) n))))
      (set (range n)))))









