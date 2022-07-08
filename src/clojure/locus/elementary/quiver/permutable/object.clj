(ns locus.elementary.quiver.permutable.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import [locus.elementary.function.core.object SetFunction]
           [locus.elementary.relation.binary.sr SeqableRelation]
           (locus.elementary.quiver.core.object Quiver)))

; This is the topos of quivers except with an extra arrow defining the inverse
; of any edge, which leads to a different presheaf topos. Then this leads to the topos
; theory of undirected graphs, as any undirected graph can be treated as a thin
; permutable quiver and there is an equivalence of categories between undirected
; graphs and the subcategory of thin permutable quivers in this topos.

; A general protocol for permutable quivers as well as groupoids
(defprotocol StructuredPermutableQuiver
  "A permutable quiver is a quiver equipped with a permutation operation on its edges, that
   flips the direction of its arrows. It forms a special topos of presheaves."
  (underlying-permutable-quiver [this]
    "Get the underlying permutable quiver of a structure.")
  (invert-morphism [this morphism]
    "Get the inverse permutation of a morphism in this structured quiver."))

; Objects in the topos of permutable quivers
; Permutable quivers appear in the topos theory of undirected graphs. Indeed, we can consider
; an undirected graph to be a thin permutable quiver.
(defrecord PermutableQuiver [edges vertices source-function target-function inv]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] (Quiver. edges vertices source-function target-function))
  (source-fn [this] source-function)
  (target-fn [this] target-function)
  (transition [this obj] (list (source-function obj) (target-function obj)))

  StructuredPermutableQuiver
  (underlying-permutable-quiver [this] this)
  (invert-morphism [this morphism] (inv morphism)))

(derive ::permutable-quiver :locus.elementary.function.core.protocols/structured-quiver)
(derive ::thin-permutable-quiver ::permutable-quiver)
(derive PermutableQuiver ::permutable-quiver)

; Get the inverse function from a permutable quiver data type
(defmethod inverse-function PermutableQuiver
  [^PermutableQuiver quiv]

  (->SetFunction
    (morphisms quiv)
    (morphisms quiv)
    (fn [edge]
      (invert-morphism quiv edge))))

; Invert a set of morphisms
(defn inverse-morphisms
  [quiv coll]

  (map
    (fn [i]
      (invert-morphism quiv i))
    coll))

; Visualize permutable quivers
(defmethod visualize PermutableQuiver
  [^PermutableQuiver quiv]

  (visualize (underlying-multirelation quiv)))

; Get all involution morphisms of the quiver
(defn involution-morphisms
  [quiv]

  (set
    (filter
      (fn [i]
        (= (invert-morphism quiv i) i))
      (morphisms quiv))))

; Constructors for permutable quivers
; Adjoin inverses to a quiver to get a permutable one
(defn adjoin-inverses
  [quiv inv]

  (->PermutableQuiver
    (morphisms quiv)
    (objects quiv)
    (source-fn quiv)
    (target-fn quiv)
    inv))

(defn singular-permutable-quiver
  [morphisms obj inv]

  (->PermutableQuiver
    morphisms
    #{obj}
    (constantly obj)
    (constantly obj)
    inv))

; Permutable quivers from symmetric relations
(defn symmetric-relation->permutable-quiver
  ([rel]
   (symmetric-relation->permutable-quiver (vertices rel) rel))

  ([coll rel]

   (PermutableQuiver. rel coll first second reverse)))

(defn symmetric-multirelation->permutable-quiver
  ([rel]
   (symmetric-multirelation->permutable-quiver (vertices rel) rel))

  ([coll rel]

   (PermutableQuiver.
     (binary-multirelation->tagged-ternary-relation rel)
     coll
     first
     second
     (fn [[a b n]]
       (list b a n)))))

; A multimethod for conversions to permutable quivers
(defmulti to-permutable-quiver type)

(defmethod to-permutable-quiver PermutableQuiver
  [quiv] quiv)

(defmethod to-permutable-quiver :default
  [coll]

  (symmetric-relation->permutable-quiver coll))

; Duals of permutable quivers
(defmethod dual PermutableQuiver
  [^PermutableQuiver quiv]

  (PermutableQuiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)
    (.inv quiv)))

; Products and coproducts in the topos of permutable quivers
(defmethod product PermutableQuiver
  [& quivers]

  (PermutableQuiver.
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
        (fn [i v]
          (invert-morphism (nth quivers i) v))
        coll))))

(defmethod coproduct PermutableQuiver
  [& quivers]

  (PermutableQuiver.
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (fn [[i v]]
      (list i (source-element (nth quivers i) v)))
    (fn [[i v]]
      (list i (target-element (nth quivers i) v)))
    (fn [[i v]]
      (list i (invert-morphism (nth quivers i) v)))))

; Subobjects of permutable quivers
(defn permutable-subquiver?
  [quiv new-edges new-vertices]

  (and
    (subquiver? quiv new-edges new-vertices)
    (superset? (inverse-morphisms quiv new-edges) new-edges)))

(defn permutable-subquiver
  [quiv new-in new-out]

  (PermutableQuiver.
    new-in
    new-out
    (source-fn quiv)
    (target-fn quiv)
    (.inv quiv)))

; Ontology of permutable quivers
(defmulti permutable-quiver? type)

(defmethod permutable-quiver? ::permutable-quiver
  [quiv] true)

(defmethod permutable-quiver? :default
  [quiv] false)

; Special classes of permutable quivers
(defn thin-permutable-quiver?
  [quiv]

  (and
    (permutable-quiver? quiv)
    (universal? (underlying-multirelation quiv))))

(defn coreflexive-thin-permutable-quiver?
  [quiv]

  (and
    (thin-permutable-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

(defn reflexive-thin-permutable-quiver?
  [quiv]

  (and
    (thin-permutable-quiver? quiv)
    (reflexive? (underlying-relation quiv))))

(defn irreflexive-thin-permutable-quiver?
  [quiv]

  (and
    (thin-permutable-quiver? quiv)
    (irreflexive? (underlying-relation quiv))))