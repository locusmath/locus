(ns locus.algebra.groupoid.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.order.general.symmetric.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.copresheaf.quiver.dependency.object :refer :all]
            [locus.set.copresheaf.quiver.dependency.thin-object :refer :all]
            [locus.set.copresheaf.bijection.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.group.core.object Group)
           (locus.algebra.category.core.object Category)
           (locus.order.general.symmetric.object Setoid)
           (locus.set.copresheaf.quiver.dependency.object DependencyQuiver)
           (locus.set.copresheaf.quiver.dependency.thin_object ThinDependencyQuiver)))

; A category C has isomorphisms for every object. A groupoid is a category C for which each
; morphism is an isomorphism, meaning that if f: A -> B is a morphism there always exists
; a f^(-1) : B -> A such that ff^(-1) and f^(-1)f both compose to identities. We implement
; this inverse function in the Groupoid class by storing it in the inv field of a Groupoid
; object. Groupoids are therefore categories with additional structure. We also provide
; conversion routines for groups and setoids to convert them to groupoids.

(deftype Groupoid [quiver op]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] (underlying-quiver quiver))
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (identity-morphism-of quiver obj))
  (underlying-unital-quiver [this] (underlying-unital-quiver quiver))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms quiver))

  StructuredPermutableQuiver
  (underlying-permutable-quiver [this] (underlying-permutable-quiver quiver))
  (invert-morphism [this x] (invert-morphism quiver x))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this] quiver)

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; The position of groupoids within the type hierarchy
(derive Groupoid :locus.set.copresheaf.structure.core.protocols/groupoid)

; Underlying relations and related notions
(defmethod underlying-relation Groupoid
  [^Groupoid obj] (underlying-relation (.-quiver obj)))

(defmethod underlying-multirelation Groupoid
  [^Groupoid obj] (underlying-multirelation (.-quiver obj)))

(defmethod visualize Groupoid
  [^Groupoid obj] (visualize (.-quiver obj)))

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
      (invert-morphism groupoid elem))))

; A mechanism for creating thin groupoids
(defn thin-groupoid
  ([rel]
   (thin-groupoid (vertices rel) rel))
  ([vertices rel]
   (Groupoid.
     (ThinDependencyQuiver. vertices rel)
     compose-ordered-pairs)))

; Conversion routines for groupoids
(defmulti to-groupoid type)

(defmethod to-groupoid Groupoid
  [groupoid] groupoid)

(defmethod to-groupoid Group
  [group]

  (Groupoid.
    (underlying-dependency-quiver group)
    group))

(defmethod to-groupoid Setoid
  [setoid]

  (let [vertices (underlying-set setoid)
        edges (underlying-relation setoid)]
    (thin-groupoid vertices edges)))

(defmethod to-groupoid :locus.set.logic.core.set/universal
  [rel]

  (thin-groupoid rel))

; The underlying groupoid of the topos of sets
(def groupoid-of-sets
  (Groupoid.
    (->DependencyQuiver
     bijection?
     universal?
     inputs
     outputs
     identity-bijection
     inv)
    (fn [[a b]]
      (compose a b))))

; Adjoin composition to dependency quivers
(defmethod adjoin-composition DependencyQuiver
  [quiv f]

  (->Groupoid quiv f))

; Products and coproducts in the category of groupoids
(defmethod product Groupoid
  [& groupoids]

  (->Groupoid
    (apply product (map underlying-dependency-quiver groupoids))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        groupoids))))

(defmethod coproduct Groupoid
  [& groupoids]

  (->Groupoid
    (apply coproduct (map underlying-dependency-quiver groupoids))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth groupoids i)]
          (list i (c (list v w))))))))

(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/group
  [& groups]

  (apply coproduct (map to-groupoid groups)))

; Opposite categories of groupoids
(defmethod dual :locus.set.copresheaf.structure.core.protocols/groupoid
  [groupoid]

  (->Groupoid
    (dual (underlying-dependency-quiver groupoid))
    (comp groupoid reverse)))

; Get underlying groupoids of categories
(defmulti underlying-groupoid type)

(defmethod underlying-groupoid :locus.set.copresheaf.structure.core.protocols/category
  [category]

  (->Groupoid
    (->DependencyQuiver
      (isomorphism-elements category)
      (objects category)
      (source-fn category)
      (target-fn category)
      (fn [obj]
        (identity-morphism-of category obj))
      (fn [morphism]
        (first (inverse-elements category morphism))))
    category))

; Get the endomorphism group of an object of a groupoid
(defn endomorphism-group
  [groupoid x]

  (->Group
    (quiver-hom-class groupoid x x)
    groupoid
    (identity-morphism-of groupoid x)
    (fn [x]
      (invert-morphism groupoid x))))

; Subobjects in the category of groupoids
(defn restrict-groupoid
  [groupoid new-morphisms new-objects]

  (->Groupoid
    (dependency-subquiver (underlying-dependency-quiver groupoid) new-morphisms new-objects)
    (fn [[a b]]
      (groupoid (list a b)))))

(defn full-subgroupoid
  [groupoid new-objects]

  (->Groupoid
    (full-dependency-subquiver (underlying-dependency-quiver groupoid) new-objects)
    (fn [[a b]]
      (groupoid (list a b)))))

(defn wide-subgroupoid
  [groupoid new-morphisms]

  (->Groupoid
    (wide-dependency-subquiver (underlying-dependency-quiver groupoid) new-morphisms)
    (fn [[a b]]
      (groupoid (list a b)))))

(defn subgroupoid?
  [groupoid new-morphisms new-objects]

  (and
    (dependency-subquiver? (underlying-dependency-quiver groupoid) new-morphisms new-objects)
    (compositionally-closed-set? groupoid new-morphisms)))

(defn enumerate-subgroupoids
  [groupoid]

  (set
    (filter
      (fn [[a b]]
        (compositionally-closed-set? groupoid a))
      (dependency-subquivers (underlying-dependency-quiver groupoid)))))

; Congruences in the category of groupoids
(defn groupoid-congruence?
  [groupoid in-partition out-partition]

  (and
    (dependency-quiver-congruence? (underlying-dependency-quiver groupoid) in-partition out-partition)
    (compositional-congruence? groupoid in-partition)))

(defn enumerate-groupoid-congruences
  [groupoid]

  (set
    (filter
      (fn [[in-partition out-partition]]
        (compositional-congruence? groupoid in-partition))
      (dependency-quiver-congruences (underlying-dependency-quiver groupoid)))))
