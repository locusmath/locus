(ns locus.elementary.quiver.unital.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           [locus.elementary.relation.binary.sr SeqableRelation]
           (locus.elementary.quiver.core.object Quiver)))

; A category is a structure equipped with a set of arrows between points having
; a source function, a target function, identities for each object, and the
; composition of arrows. A quiver handles the source and the target functions,
; but it is also necessary to have something that can handle the data of a
; quiver equipped with an identity function, which is to say a category without
; its composition function. This is handled by the topos of unital quivers, and
; so with this topos in mind we can consider categories to be presheaves
; constructed by the product of a unital quiver and a function.

; Generalized unital quivers
(defprotocol StructuredUnitalQuiver
  "Let Quiv be the category of quivers. Then we can enrich quiv with an extra arrow
   id: V -> E that maps each vertex to its identity morphism."

  (underlying-unital-quiver [this]
    "Get the underlying unital quiver of a structure such as a category.")

  (identity-morphism-of [this obj]
    "Get the identity morphism of an object"))

; Presheaves in the topos of unital quivers
(deftype UnitalQuiver [edges vertices source-function target-function id]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] (Quiver. edges vertices source-function target-function))
  (source-fn [this] source-function)
  (target-fn [this] target-function)
  (transition [this obj] (list (source-function obj) (target-function obj)))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] this)
  (identity-morphism-of [this obj] (id obj)))

(derive UnitalQuiver :locus.elementary.copresheaf.core.protocols/structured-unital-quiver)

; Identity element functions of structured quivers
(defn identity-element-function
  [quiv]

  (->SetFunction
    (objects quiv)
    (morphisms quiv)
    (fn [obj]
      (identity-morphism-of quiv obj))))

(defn source-identity
  [quiv morphism]

  (identity-morphism-of quiv (source-element quiv morphism)))

(defn target-identity
  [quiv morphism]

  (identity-morphism-of quiv (target-element quiv morphism)))

(defn source-identity-function
  [quiv]

  (->SetFunction
    (morphisms quiv)
    (morphisms quiv)
    (fn [morphism]
      (source-identity quiv morphism))))

(defn target-identity-function
  [quiv]

  (->SetFunction
    (morphisms quiv)
    (morphisms quiv)
    (fn [morphism]
      (target-identity quiv morphism))))

; Get the identity morphisms of a collection of vertices
(defn identity-morphisms-of
  [quiv coll]

  (set
    (map
      (fn [i]
        (identity-morphism-of quiv i))
      coll)))

; Get all identity morphisms of a structured unital quiver
(defn identity-morphisms
  [quiv]

  (map
    (fn [obj]
      (identity-morphism-of quiv obj))
    (objects quiv)))

(defn nonidentity-morphisms
  [quiv]

  (difference
    (set (morphisms quiv))
    (set (identity-morphisms quiv))))

(defn nonidentity-endomorphisms
  [quiv x]

  (disj
    (quiver-hom-class quiv x x)
    (identity-morphism-of quiv x)))

; Visualize unital quivers
(defmethod visualize UnitalQuiver
  [^UnitalQuiver quiv]

  (visualize (underlying-multirelation quiv)))

; Adjoin identities to an existing quiver
(defn adjoin-identities
  [quiv id]

  (->UnitalQuiver (morphisms quiv) (objects quiv) (source-fn quiv) (target-fn quiv) id))

; Create a unital quiver from a pair of edge maps
(defn invert-hash-map
  [coll]

  (let [pairs (seq coll)
        pair-firsts (map first pairs)
        pair-seconds (map second pairs)]
    (zipmap pair-seconds pair-firsts)))

(defn create-unital-quiver
  [identity-map nonidentity-edge-map]

  (let [all-vertices (set (keys identity-map))
        identity-edges (set (vals identity-map))
        all-edges (union
                    identity-edges
                    (set (keys nonidentity-edge-map)))
        inverse-identity-map (invert-hash-map identity-map)]
    (UnitalQuiver.
      all-edges
      all-vertices
      (fn [x]
        (if (contains? identity-edges x)
          (inverse-identity-map x)
          (first (nonidentity-edge-map x))))
      (fn [x]
        (if (contains? identity-edges x)
          (inverse-identity-map x)
          (second (nonidentity-edge-map x))))
      (fn [e]
        (identity-map e)))))

; Convert a reflexive relation into a unital quiver
(defmulti to-unital-quiver type)

(defmethod to-unital-quiver UnitalQuiver
  [^UnitalQuiver quiver] quiver)

(defmethod to-unital-quiver :default
  [rel]

  (->UnitalQuiver
    rel
    (vertices rel)
    first
    second
    (fn [i]
      (list i i))))

; Create unital quivers by sets of morphisms and objects
(defn as-unital-quiver
  [morphisms objects]

  (->UnitalQuiver
    morphisms
    objects
    source-object
    target-object
    identity-morphism))

; Singular unital quivers
(defn singular-unital-quiver
  [coll obj id]

  (->UnitalQuiver
    coll
    #{obj}
    (constantly obj)
    (constantly obj)
    (constantly id)))

; Duals of unital quivers
(defmethod dual UnitalQuiver
  [^UnitalQuiver quiv]

  (UnitalQuiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)
    (.id quiv)))

; Products and coproducts in the topos of unital quivers
(defmethod product UnitalQuiver
  [& quivers]

  (UnitalQuiver.
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
        coll))))

(defmethod coproduct UnitalQuiver
  [& quivers]

  (UnitalQuiver.
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (fn [[i v]]
      (list i (source-element (nth quivers i) v)))
    (fn [[i v]]
      (list i (target-element (nth quivers i) v)))
    (fn [[i obj]]
      (list i (identity-morphism-of (nth quivers i) obj)))))

; Subobjects of unital quivers
(defn unital-subquiver?
  [q new-edges new-vertices]

  (and
    (subquiver? q new-edges new-vertices)
    (superset? (list (identity-morphism-of q new-vertices) new-edges))))

(defn unital-subquiver
  [q new-edges new-vertices]

  (UnitalQuiver.
    new-edges
    new-vertices
    (source-fn q)
    (target-fn q)
    (.id q)))

; Ontology of unital quivers
; These classify the unital quivers based upon their basic properties as elements
; of the elementary topos of copresheaves over their index category.
(defn unital-quiver?
  [quiv]

  (= (type quiv) UnitalQuiver))

(defn coreflexive-unital-quiver?
  [quiv]

  (and
    (unital-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

(defn antisymmetric-unital-quiver?
  [quiv]

  (and
    (unital-quiver? quiv)
    (antisymmetric? (underlying-relation quiv))))

(defn thin-unital-quiver?
  [quiv]

  (and
    (unital-quiver? quiv)
    (universal? (underlying-multirelation quiv))))

(defn coreflexive-thin-unital-quiver?
  [quiv]

  (and
    (unital-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))