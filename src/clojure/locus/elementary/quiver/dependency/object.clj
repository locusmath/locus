(ns locus.elementary.quiver.dependency.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all])
  (:import [locus.elementary.function.core.object SetFunction]
           [locus.elementary.relation.binary.sr SeqableRelation]
           (locus.elementary.quiver.core.object Quiver)))

; The topos of dependency quivers consists of quivers equipped also with an identity function
; and a transpose function. A dependency quiver handles all the data of a groupoid, except
; for its composition function. Categories and groupoids are distinguished by their underlying
; quivers: categories are constructed over unital quivers while groupoids are constructed
; over dependency quivers. The main application of these presheaves are to model aspects
; of the theory of groupoids.

; A general protocol for dependency quivers
(defprotocol StructuredDependencyQuiver
  "A dependency quiver is a quiver equipped with both an identity function and an inverse function. They
   include the underlying quivers of groupoids."

  (underlying-dependency-quiver [this]
   "Get the underlying dependency quiver of a structure"))

; Objects in the topos of dependency quivers
(defrecord DependencyQuiver [edges vertices source-function target-function id inv]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] (Quiver. edges vertices source-function target-function))
  (source-fn [this] source-function)
  (target-fn [this] target-function)
  (transition [this obj] (list (source-function obj) (target-function obj)))

  StructuredPermutableQuiver
  (underlying-permutable-quiver [this]
    (->PermutableQuiver edges vertices source-function target-function inv))
  (invert-morphism [this x] (inv x))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver edges vertices source-function target-function id))
  (identity-morphism-of [this obj] (id obj))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this] this))

(derive DependencyQuiver :locus.elementary.function.core.protocols/structured-quiver)

(defmethod visualize DependencyQuiver
  [^DependencyQuiver quiv]

  (visualize (underlying-multirelation quiv)))

; Inverse functions
(defmethod inverse-function DependencyQuiver
  [^DependencyQuiver quiv]

  (->SetFunction
    (morphisms quiv)
    (morphisms quiv)
    (fn [edge]
      (invert-morphism quiv edge))))

; Adjoin dependencies on to an ordinary quiver in order to get a dependency quiver
(defn adjoin-dependencies
  [quiv id inv]

  (->DependencyQuiver
    (morphisms quiv)
    (objects quiv)
    (source-fn quiv)
    (target-fn quiv)
    id
    inv))

(defn singular-dependency-quiver
  [morphisms obj id inv]

  (->DependencyQuiver
    morphisms
    #{obj}
    (constantly obj)
    (constantly obj)
    id
    inv))

; Convert a dependency relation in to a dependency quiver
(defn to-dependency-quiver
  [rel]

  (->DependencyQuiver
    rel
    (vertices rel)
    first
    second
    (fn [i]
      (list i i))
    reverse))

; Duals of dependency quivers
(defmethod dual DependencyQuiver
  [^DependencyQuiver quiv]

  (DependencyQuiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)
    (.id quiv)
    (.inv quiv)))

; Products and coproducts in the topos of dependency quivers
(defmethod product DependencyQuiver
  [& quivers]

  (DependencyQuiver.
    (apply cartesian-product (map morphisms quivers))
    (apply cartesian-product (map objects quivers))
    (fn [coll]
      (map-indexed
        (fn [i v]
          (source-element (nth quivers i) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          (target-element (nth quivers i) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i obj]
          (identity-morphism-of (nth quivers i) obj))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          (invert-morphism (nth quivers i) v))
        coll))))

(defmethod coproduct DependencyQuiver
  [& quivers]

  (DependencyQuiver.
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (fn [[i v]]
      (list i (source-element (nth quivers i) v)))
    (fn [[i v]]
      (list i (target-element (nth quivers i) v)))
    (fn [[i obj]]
      (list i (identity-morphism-of (nth quivers i) obj)))
    (fn [[i v]]
      (list i (invert-morphism (nth quivers i) v)))))

; Subobjects of dependency quivers
(defn dependency-subquiver?
  [quiv new-edges new-vertices]

  (and
    (subquiver? quiv new-edges new-vertices)
    (superset? (list (identity-morphism-of quiv new-vertices) new-edges))
    (superset? (inverse-morphisms quiv new-edges) new-edges)))

(defn dependency-subquiver
  [quiv new-in new-out]

  (DependencyQuiver.
    new-in
    new-out
    (source-fn quiv)
    (target-fn quiv)
    (.id quiv)
    (.inv quiv)))

; Ontology of dependency quivers
(defn dependency-quiver?
  [quiv]

  (= (type quiv) DependencyQuiver))

(defn thin-dependency-quiver?
  [quiv]

  (and
    (dependency-quiver? quiv)
    (universal? (underlying-multirelation quiv))))