(ns locus.algebra.group.permutation.permutation-group
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.effects.global.permutation :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.algebra.group.core.morphism :refer :all]
            [locus.algebra.group.core.aut :refer :all]
            [locus.algebra.category.hom.sethom :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.base.effects.global.permutation Permutation)
           (locus.base.function.core.object SetFunction)
           (locus.algebra.group.core.morphism GroupMorphism)))

; Let G be a concrete category containing only one object for which each morphism is an isomorphism. Then
; each element of G is naturally represented by its set valued functor as a permutation, and it follows
; that G is a permutation group. This file deals with this fundamental aspect of fundamental group theory.

(deftype PermutationGroup [elems op id inv coll action]
  ConcreteObject
  (underlying-set [this] elems)

  ; Permutation groups are categories and therefore quivers
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
  (invoke [this obj]
    (op obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args))

  ; Permutation groups are concrete categories
  ConcreteCategoricalStructure
  (object-to-set [this obj] coll)
  (morphism-to-function [this morphism] (SetFunction. coll coll (fn [x] (action morphism x)))))

; Permutation groups are both groups and concrete categories
(derive PermutationGroup :locus.elementary.copresheaf.core.protocols/concrete-group)

; Parts of permutation groups
(defmethod identity-elements PermutationGroup
  [group]

  #{(.id group)})

(defmethod to-mset PermutationGroup
  [monoid]

  (->MSet monoid (.coll monoid) (.action monoid)))

; Permutation group conversion
(defn extend-group
  [group coll action]

  (PermutationGroup.
    (underlying-set group)
    (.op group)
    (identity-element group)
    (.inv group)
    coll
    action))

(defmulti to-permutation-group type)

(defmethod to-permutation-group PermutationGroup
  [group] group)

(defmethod to-permutation-group Permutation
  [perm]

  (extend-group
    (cyclic-group (permutation-period perm))
    (underlying-set perm)
    (partial iteratively-apply perm)))

; Get a permutation from an element
(defn permutation-element
  [group action]

  (Permutation.
    (.coll group)
    (fn [x]
      ((.action group) action x))
    (fn [x]
      ((.action group) ((.inv group) action) x))))

; Let G be a concrete group associated with a set-valued functor F: G -> Sets
; then given a functor f : H -> G -> Sets we can induce by composition a
; functor f : H -> Sets which makes the input category H into a concrete category.
; By this process every subgroup of a concrete category is again concrete.
(defn restrict-permutation-group
  [^PermutationGroup group, coll]

  (PermutationGroup.
    coll
    (.op group)
    (.id group)
    (.inv group)
    (.coll group)
    (.action group)))

; Filtering is a basic generalisation of restriction
(defn filter-permutation-group
  [func, ^PermutationGroup group]

  (restrict-permutation-group
    group
    (filter func (underlying-set group))))

; Get the orbit of an element of a permutation group
(defn element-orbit
  [group elem]

  (set
    (map
      (fn [action]
        ((.action group) action elem))
      (underlying-set group))))

(defn orbits
  [group]

  (loop [remaining-values (set (.coll group))
         rval #{}]
    (if (empty? remaining-values)
      rval
      (let [selected-element (first remaining-values)
            selected-orbit (element-orbit group selected-element)]
        (recur
          (difference remaining-values selected-orbit)
          (conj rval selected-orbit))))))

(defn invariant-sets
  [group]

  (let [coll (orbits group)]
    (set
      (map
        (fn [orbit-collection]
          (apply union orbit-collection))
        (power-set coll)))))

; A distinguishing factor of permutation groups is that stabilizers produce subobjects
(defn element-stabilizer
  [group elem]

  (filter-permutation-group
    (fn [action]
      (= ((.action group) action elem) elem))
    group))

(defn pointwise-set-stabilizer
  [group coll]

  (filter-permutation-group
    (fn [action]
      (every?
        (fn [i]
          (= ((.action group) action i) i))
        coll))
    group))

(defn setwise-set-stabilizer
  [group coll]

  (filter-permutation-group
    (fn [action]
      (every?
        (fn [i]
          (coll ((.action group) action i)))
        coll))
    group))

(defn restrict-orbit
  [group partition]

  (filter-permutation-group
    (fn [action]
      (permutation-in-orbit? (permutation-element group action) partition))
    group))

(defn lens-group-restriction
  [group active-partition stable-partition]

  (filter-permutation-group
    (fn [i]
      (lens-member-permutation? (permutation-element group i) active-partition stable-partition))
    group))

; Embed the permutation group within a larger group
(defn permutation-group-embedding
  [group]

  (GroupMorphism.
    group
    (aut (underlying-set group))
    (fn [elem]
      (morphism-to-function group elem))))

; Create a permutation group from a set of permutations
(defn seqable-permutations
  [coll]

  (->SeqableUniversal
    (fn [i]
      (and
        (endofunction? i)
        (= (inputs i) coll)))
    (map to-permutation (enumerate-permutation-maps (vec coll)))
    {:count (factorial (count coll))}))

(defn as-permutation-group
  [coll permutations]

  (PermutationGroup.
    permutations
    (fn [[f g]]
      (compose f g))
    (identity-permutation coll)
    inv
    coll
    (fn [permutation x] (permutation x))))

(defn invariant-reduction
  [group coll]

  (as-permutation-group
    coll
    (set
      (map
        (fn [i]
          (let [perm (permutation-element group i)]
            (restrict-permutation perm coll)))
        (underlying-set group)))))

(defn sym
  [coll]

  (as-permutation-group
    coll
    (seqable-permutations coll)))

(defn alternating-group
  [coll]

  (filter-permutation-group even-permutation? (sym coll)))

(defn lens-permutation-group
  [active-partition stable-partition]

  (lens-group-restriction (sym (apply union active-partition)) active-partition stable-partition))

(defn orbit-symmetric-permutation-group
  [partition]

  (let [coll (apply union partition)]
    (restrict-orbit (sym coll) partition)))

(defn display-permutations
  [group]

  (doseq [i (underlying-set group)]
    (prn (cycle-decomposition (permutation-element group i)))))





