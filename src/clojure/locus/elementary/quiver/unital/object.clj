(ns locus.elementary.quiver.unital.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           [locus.quiver.relation.binary.sr SeqableRelation]
           (locus.quiver.binary.core.object Quiver)))

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

(derive ::unital-quiver :locus.elementary.copresheaf.core.protocols/structured-unital-quiver)
(derive ::thin-unital-quiver ::unital-quiver)
(derive UnitalQuiver ::unital-quiver)

; Quiver source and target identity maps
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

; Get the sets and functions of a unital quiver
(defmethod get-set ::unital-quiver
  [quiver x]

  (case x
    0 (morphisms quiver)
    1 (objects quiver)))

(defmethod get-function ::unital-quiver
  [quiver x]

  (case x
    0 (identity-function (morphisms quiver))
    1 (identity-function (objects quiver))
    2 (source-function quiver)
    3 (target-function quiver)
    4 (identity-element-function quiver)
    5 (source-identity-function quiver)
    6 (target-identity-function quiver)))

; Adjoin identities to an existing quiver
(defn adjoin-identities
  [quiv id]

  (->UnitalQuiver
    (morphisms quiv)
    (objects quiv)
    (source-fn quiv)
    (target-fn quiv)
    id))

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

; Singular unital quivers
(defn singular-unital-quiver
  [coll obj id]

  (->UnitalQuiver
    coll
    #{obj}
    (constantly obj)
    (constantly obj)
    (constantly id)))

(defn coreflexive-relational-unital-quiver
  [coll]

  (->UnitalQuiver
    (coreflexive-relation coll)
    coll
    first
    second
    (fn [i]
      (list i i))))

(defn relational-unital-quiver
  ([rel]
   (relational-unital-quiver (vertices rel) rel))
  ([vertices rel]
   (->UnitalQuiver
     rel
     vertices
     first
     second
     (fn [i]
       (list i i)))))

(defn complete-relational-unital-quiver
  [coll]

  (->UnitalQuiver
    (->CompleteRelation coll)
    coll
    first
    second
    (fn [i]
      (list i i))))

; Multimethods for converting various objects into unital quivers
(defmulti to-unital-quiver type)

(defmethod to-unital-quiver UnitalQuiver
  [^UnitalQuiver quiver] quiver)

(defmethod to-unital-quiver :locus.base.logic.core.set/universal
  [rel] (relational-unital-quiver rel))

(defmethod to-unital-quiver :default
  [obj] (underlying-unital-quiver obj))

; Create unital quivers by sets of morphisms and objects
(defn as-unital-quiver
  [morphisms objects]

  (->UnitalQuiver
    morphisms
    objects
    source-object
    target-object
    identity-morphism))

; Underlying relations and multirelations of unital quivers
(defmethod underlying-multirelation UnitalQuiver
  [^UnitalQuiver quiver]

  (multiset
    (map
      (fn [e]
        (transition quiver e))
      (morphisms quiver))))

(defmethod underlying-relation UnitalQuiver
  [^UnitalQuiver quiver]

  (set (underlying-multirelation quiver)))

; Visualize unital quivers
(defmethod visualize UnitalQuiver
  [^UnitalQuiver quiv]

  (visualize (underlying-multirelation quiv)))

; Products and coproducts in the topos of unital quivers
(defmethod product ::unital-quiver
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

(defmethod coproduct ::unital-quiver
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

; Duals of unital quivers
(defmethod dual UnitalQuiver
  [^UnitalQuiver quiv]

  (UnitalQuiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)
    (.id quiv)))

; Test for identity elements of a unital quiver
(defn identity-element?
  [quiv elem]

  (let [source (source-element quiv elem)
        target (target-element quiv elem)]
    (and
      (= source target)
      (= (identity-morphism-of quiv source) elem))))

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

; Statistics for unital quivers
(defn number-of-identity-morphisms
  [quiver]

  (count (identity-morphisms quiver)))

(defn number-of-nonidentity-morphisms
  [quiver]

  (count (nonidentity-morphisms quiver)))

; Unital subquivers
(defn unital-subquiver
  [q, new-edges, new-vertices]

  (UnitalQuiver.
    new-edges
    new-vertices
    (source-fn q)
    (target-fn q)
    (fn [obj]
      (identity-morphism-of q obj))))

(defn wide-unital-subquiver
  [quiver new-edges]

  (unital-subquiver
    quiver
    new-edges
    (objects quiver)))

(defn full-unital-subquiver
  [quiver new-objects]

  (unital-subquiver
    quiver
    (quiver-set-inverse-image quiver new-objects)
    new-objects))

; Subobjects of unital quivers
(defn unital-subquiver?
  [q new-edges new-vertices]

  (and
    (subquiver? q new-edges new-vertices)
    (superset? (list (identity-morphisms-of q new-vertices) new-edges))))

(defn unital-quiver-morphism-set-closure
  [quiv morphism-set]

  (apply
    union
    (map
      (fn [morphism]
        (set
          (list
            (source-identity quiv morphism)
            (target-identity quiv morphism)
            morphism)))
      morphism-set)))

(defn unital-subquiver-closure
  [quiv morphism-set object-set]

  (let [initial-morphisms (union
                            (identity-morphisms-of quiv object-set)
                            morphism-set)
        closed-morphism-set (unital-quiver-morphism-set-closure quiv initial-morphisms)]
    (list
      closed-morphism-set
      (quiver-set-image quiv closed-morphism-set))))

; Enumeration theory for unital subqivers
(defn unital-subquivers-by-object-set
  [quiv output-set]

  (let [all-identities (identity-morphisms-of quiv output-set)
        possible-morphisms (difference
                             (quiver-set-inverse-image quiv output-set)
                             all-identities)]
    (map
      (fn [morphism-set]
        (list
          (union all-identities morphism-set)
          output-set))
      (power-set possible-morphisms))))

(defn unital-subquivers
  [quiv]

  (mapcat
    (fn [object-set]
      (unital-subquivers-by-object-set quiv object-set))
    (power-set (objects quiv))))

; Relations on subobjects of unital quivers
(defn covering-unital-subquivers
  [quiv in-set out-set]

  (concat
    (map
      (fn [new-object]
        (list
          (conj in-set (identity-morphism-of quiv new-object))
          (conj out-set new-object)))
      (difference (objects quiv) out-set))
    (for [i (difference (morphisms quiv) in-set)
          :when (and
                  (contains? out-set (source-element quiv i))
                  (contains? out-set (target-element quiv i)))]
      (list
        (conj in-set i)
        out-set))))

(defn unital-subquivers-covering
  [quiv]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (covering-unital-subquivers quiv in-set out-set)))
      (unital-subquivers quiv))))

; Quotients of unital quivers
(defn unital-quiver-quotient
  [quiver in-partition out-partition]

  (UnitalQuiver.
    in-partition
    out-partition
    (fn [part]
      (projection out-partition (source-element quiver (first part))))
    (fn [part]
      (projection out-partition (target-element quiver (first part))))
    (fn [obj]
      (projection in-partition (identity-morphism-of quiver obj)))))

; Congruences of unital quivers
(defn unital-quiver-congruence?
  [quiver in-partition out-partition]

  (and
    (quiver-congruence? quiver in-partition out-partition)
    (io-relation? (identity-element-function quiver) out-partition in-partition)))

; Enumerate all the congruences of a unital quiver
(defn minimal-morphism-partition-by-object-partition
  [quiver object-partition]

  (union
    (set
      (map
       (fn [morphism]
         #{morphism})
       (nonidentity-morphisms quiver)))
    (set
      (map
        (fn [part]
          (set
            (map
              (fn [object]
                (identity-morphism-of quiver object))
              part)))
        object-partition))))

(defn unital-quiver-morphism-partitions-by-object-partition
  [quiver object-partition]

  (partitions-interval
    (minimal-morphism-partition-by-object-partition quiver object-partition)
    (quiver-partition-inverse-image quiver object-partition)))

(defn unital-quiver-congruences-by-object-partition
  [quiver object-partition]

  (map
    (fn [morphism-partition]
      (list morphism-partition object-partition))
    (unital-quiver-morphism-partitions-by-object-partition quiver object-partition)))

(defn unital-quiver-congruences
  [quiver]

  (set
    (mapcat
      (fn [object-partition]
        (unital-quiver-congruences-by-object-partition quiver object-partition))
      (enumerate-set-partitions (objects quiver)))))

; Construct the covering relation of the congruence lattice of a unital quiver
(defn unital-quiver-covering-congruences
  [quiver in-partition out-partition]

  (union
    (set
      (map
        (fn [new-out-partition]
          (list
            (join-set-partitions
              (minimal-morphism-partition-by-object-partition quiver new-out-partition)
              in-partition)
            new-out-partition))
        (direct-set-partition-coarsifications out-partition)))
    (set
      (for [i (direct-set-partition-coarsifications in-partition)
            :when (set-superpartition?
                    (list
                      (quiver-partition-image quiver i)
                      out-partition))]
        (list i out-partition)))))

(defn unital-quiver-congruences-covering
  [quiver]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list [in-partition out-partition] [new-in-partition new-out-partition]))
          (unital-quiver-covering-congruences quiver in-partition out-partition)))
      (unital-quiver-congruences quiver))))

; Ontology of unital quivers
; These classify the unital quivers based upon their basic properties as elements
; of the elementary topos of copresheaves over their index category.
(defmulti unital-quiver? type)

(defmethod unital-quiver? ::unital-quiver
  [quiver] true)

(defmethod unital-quiver? :default
  [quiver] false)

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