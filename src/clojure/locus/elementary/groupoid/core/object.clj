(ns locus.elementary.groupoid.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.preorder.setoid.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.group.core.object Group)
           (locus.elementary.category.core.object Category)
           (locus.elementary.preorder.setoid.object Setoid)
           (locus.elementary.quiver.dependency.object DependencyQuiver)))

; A category C has isomorphisms for every object. A groupoid is a category C for which each
; morphism is an isomorphism, meaning that if f: A -> B is a morphism there always exists
; a f^(-1) : B -> A such that ff^(-1) and f^(-1)f both compose to identities. We implement
; this inverse function in the Groupoid class by storing it in the inv field of a Groupoid
; object. Groupoids are therefore categories with additional structure. We also provide
; conversion routines for groups and setoids to convert them to groupoids.

(deftype Groupoid [morphisms objects source target func id inv]
  ; Every groupoid is a structured quiver
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  StructuredPermutableQuiver
  (invert-morphism [this morphism] (inv morphism))
  (underlying-permutable-quiver [this]
    (->PermutableQuiver morphisms objects source target inv))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (id obj))
  (underlying-unital-quiver [this] (->UnitalQuiver morphisms objects source target id))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this]
    (->DependencyQuiver morphisms objects source target id inv))

  ; Groupoids are also structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; The position of groupoids within the type hierarchy
(derive Groupoid :locus.elementary.copresheaf.core.protocols/groupoid)

; Underlying relations
(defmethod underlying-relation Groupoid
  [cat] (underlying-relation (underlying-quiver cat)))

; Underlying setoids
(defn underlying-setoid
  [groupoid]

  (Setoid. (second-set groupoid) (underlying-relation groupoid)))

; The inverse function of a groupoid
(defmethod inverse-function Groupoid
  [^Groupoid groupoid]

  (->SetFunction
    (morphisms groupoid)
    (morphisms groupoid)
    (fn [elem]
      ((.inv groupoid) elem))))

; We now need some way of performing general conversions involving groupoids
(defmulti to-groupoid type)

(defmethod to-groupoid Groupoid
  [groupoid] groupoid)

(defmethod to-groupoid Group
  [group]

  (Groupoid.
    (underlying-set group)
    #{0}
    (constantly 0)
    (constantly 0)
    group
    (fn [x]
      (when (zero? x)
        (.id group)))
    (.inv group)))

(defmethod to-groupoid Setoid
  [setoid]

  (let [vertices (underlying-set setoid)
        edges (underlying-relation setoid)]
    (Groupoid.
      edges
      vertices
      first
      second
      (letfn [(compose-ordered-pairs [[[a b] [c d]]]
                (list c b))]
        compose-ordered-pairs)
      (fn [x]
        (list x x))
      reverse)))

; The groupoid of sets
(def groupoid-of-sets
  (Groupoid.
    bijection?
    universal?
    inputs
    outputs
    (fn [[a b]] (compose a b))
    identity-bijection
    inv))

; Adjoin composition operations to quivers
(defmethod adjoin-composition DependencyQuiver
  [quiv f]

  (->Groupoid
    (morphisms quiv)
    (objects quiv)
    (source-fn quiv)
    (target-fn quiv)
    f
    (.id quiv)
    (.inv quiv)))

; Products of groupoids
(defmethod product :locus.elementary.copresheaf.core.protocols/groupoid
  [& groupoids]

  (Groupoid.
    (apply cartesian-product (map first-set groupoids))
    (apply cartesian-product (map second-set groupoids))
    (fn [morphisms]
      (map-indexed
        (fn [i v]
          ((source-fn (nth groupoids i)) v))
        morphisms))
    (fn [morphisms]
      (map-indexed
        (fn [i v]
          ((target-fn (nth groupoids i)) v))
        morphisms))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        groupoids))
    (fn [obj]
      (map-indexed
        (fn [i v]
          ((.id ^Groupoid (nth groupoids i)) v))
        obj))
    (fn [obj]
      (map-indexed
        (fn [i v]
          ((.inv ^Groupoid (nth groupoids i)) v))
        obj))))

(defmethod coproduct :locus.elementary.copresheaf.core.protocols/groupoid
  [& groupoids]

  (Groupoid.
    (apply cartesian-coproduct (map first-set groupoids))
    (apply cartesian-coproduct (map second-set groupoids))
    (fn [[i v]]
      (list i ((source-fn (nth groupoids i)) v)))
    (fn [[i v]]
      (list i ((target-fn (nth groupoids i)) v)))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth groupoids i)]
          (list i (c (list v w))))))
    (fn [[i v]]
      (list i ((.id ^Groupoid (nth groupoids i)) v)))
    (fn [[i v]]
      (list i ((.inv ^Groupoid (nth groupoids i)) v)))))

(defmethod dual :locus.elementary.copresheaf.core.protocols/groupoid
  [groupoid]

  (Groupoid.
    (first-set groupoid)
    (second-set groupoid)
    (.target groupoid)
    (.source groupoid)
    (comp groupoid reverse)
    (.id groupoid)
    (.inv groupoid)))

; Coproducts of groups
(defmethod coproduct :locus.elementary.copresheaf.core.protocols/group
  [& groups]

  (apply coproduct (map to-groupoid groups)))

; Get the underlying groupoid of a category
(defmulti underlying-groupoid type)

(defmethod underlying-groupoid :locus.elementary.copresheaf.core.protocols/category
  [^Category category]

  (Groupoid.
    (isomorphism-elements category)
    (objects category)
    (.source category)
    (.target category)
    (.func category)
    (.id category)
    (fn [morphism]
      (first (inverse-elements category morphism)))))

