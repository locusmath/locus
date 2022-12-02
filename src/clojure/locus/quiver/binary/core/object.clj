(ns locus.quiver.binary.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           [locus.quiver.relation.binary.sr SeqableRelation]
           (clojure.lang IPersistentMap)))

; Objects in the topos Sets^{T_2^*}
; Let T_2^* be the totally ordered category with two objects and four morphisms.
; Then this category is the index category of a topos: the topos of quivers
; Sets^(T_2^*). In this file, we implement the routines for dealing
; with elements of this fundamental topos.

; A quiver should implement diset and the structured quiver protocol
(defprotocol StructuredQuiver
  "Let Quiv be the category of quivers. Then we can define a category C over Quiv by a forgetful functor,
  f : C->Quiv. This protocol defines methods for handling objects in such categories with reference to their
  forgetful functors to the topos of quivers."

  (underlying-quiver [this]
    "Get the output quiver of the mapping to the topos of quivers.")
  (source-fn [this]
    "The source function of the structured quiver returned as a Clojure IFn.")
  (target-fn [this]
    "The target function of the structured quiver returned as a Clojure IFn.")
  (transition [this obj]
    "This returns for a morphism f:A->B the ordered pair (A,B) called its transition."))

; A default implementation of the quiver protocol
(deftype Quiver [edges vertices source-function target-function]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [edges vertices]))

  StructuredQuiver
  (underlying-quiver [this] this)
  (source-fn [this] source-function)
  (target-fn [this] target-function)
  (transition [this obj] (list (source-function obj) (target-function obj))))

(derive Quiver :locus.quiver.base.core.protocols/quiver)

; Source and target functions
(defn source-function
  [q]

  (SetFunction. (morphisms q) (objects q) (source-fn q)))

(defn target-function
  [q]

  (SetFunction. (morphisms q) (objects q) (target-fn q)))

; Components of quivers
(defmethod get-set :locus.quiver.base.core.protocols/quiver
  [quiver x]

  (case x
    0 (morphisms quiver)
    1 (objects quiver)))

(defmethod get-function :locus.quiver.base.core.protocols/quiver
  [quiver x]

  (case x
    0 (identity-function (morphisms quiver))
    1 (identity-function (objects quiver))
    2 (source-function quiver)
    3 (target-function quiver)))

; These are very useful shorthands
(defn source-element
  [quiv elem]

  ((source-fn quiv) elem))

(defn target-element
  [quiv elem]

  ((target-fn quiv) elem))

(defmethod nth-component :locus.quiver.base.core.protocols/quiver
  [quiver edge i]

  (case i
    0 (source-element quiver edge)
    1 (target-element quiver edge)))

; Quiver source and target maps
(defn quiver-source-map
  [quiver]

  (into
    {}
    (map
      (fn [morphism]
        [morphism (source-element quiver morphism)])
      (morphisms quiver))))

(defn quiver-target-map
  [quiver]

  (into
    {}
    (map
      (fn [morphism]
        [morphism (target-element quiver morphism)])
      (morphisms quiver))))

; Generalized mechanisms for creating quivers
(defn get-nth-component-map
  [coll n]

  (apply
    merge
    (for [key (keys coll)
          :let [val (get coll key)]]
      (into
        {}
        (map
          (fn [i]
            [i (nth key n)])
          val)))))

(defn make-quiver
  [vertices hom]

  (let [edges (apply union (vals hom))
        source-map (get-nth-component-map hom 0)
        target-map (get-nth-component-map hom 1)]
    (->Quiver
      edges
      vertices
      source-map
      target-map)))

(defn create-quiver
  ([edge-map]
   (let [vertices (apply
                    union
                    (map set (vals edge-map)))]
     (create-quiver vertices edge-map)))

  ([vertices edge-map]
   (->Quiver
     (set (keys edge-map))
     vertices
     (fn [edge]
       (first (get edge-map edge)))
     (fn [edge]
       (second (get edge-map edge))))))

; Utilities for creating special types of quivers
(defn singular-quiver
  [coll obj]

  (Quiver.
    coll
    #{obj}
    (constantly obj)
    (constantly obj)))

(defn relational-quiver
  ([rel] (relational-quiver (vertices rel) rel))

  ([vertex-set rel]
   (Quiver.
     (set rel)
     vertex-set
     first
     second)))

(defn coreflexive-relational-quiver
  [coll]

  (->Quiver
    (coreflexive-relation coll)
    coll
    first
    second))

(defn complete-relational-quiver
  [coll]

  (->Quiver
    (->CompleteRelation coll)
    coll
    first
    second))

(defn binary-multirelation->tagged-ternary-relation
  [rel]

  (set
    (mapcat
      (fn [elem]
        (let [mult (multiplicity rel elem)]
          (map
            (fn [i]
              (list (first elem) (second elem) i))
            (range mult))))
      (support rel))))

(defn multirelational-quiver
  ([rel] (multirelational-quiver (vertices rel) rel))

  ([coll rel]

   (Quiver.
     (binary-multirelation->tagged-ternary-relation rel)
     coll
     first
     second)))

; An empty quiver doesn't have any edges
(defn empty-quiver
  [coll]

  (->Quiver
    #{}
    coll
    first
    second))

; Create a coreflexive quiver by taking a function and making it play the role of both
; the source and the target functions of the resulting quiver copresheaf.
(defn coreflexive-quiver
  [func]

  (->Quiver
    (inputs func)
    (outputs func)
    func
    func))

; A constant quiver has the same object and morphism set and identity component functions
(defn constant-quiver
  [coll]

  (->Quiver coll coll identity identity))

; These are useful constructors for quivers
(defmulti to-quiver type)

(defmethod to-quiver :locus.base.logic.structure.protocols/structured-function
  [func]

  (Quiver.
    (underlying-relation func)
    (union (inputs func) (outputs func))
    first
    second))

(defmethod to-quiver IPersistentMap
  [coll]

  (Quiver.
    (set (map seq coll))
    (union (set (keys coll)) (set (vals coll)))
    first
    second))

(defmethod to-quiver :locus.base.logic.core.set/universal
  [rel]

  (relational-quiver rel))

(defmethod to-quiver :default
  [rel]

  (if (multiset? rel)
    (multirelational-quiver rel)
    (underlying-quiver rel)))

; As quiver function
(defn as-quiver
  [morphisms objects]

  (->Quiver
    morphisms
    objects
    source-object
    target-object))

; Underlying relations
(defmethod underlying-multirelation :default
  [quiv]

  (multiset
    (map
      (fn [e]
        (transition quiv e))
      (morphisms quiv))))

(defmethod underlying-relation Quiver
  [quiv]

  (set (underlying-multirelation quiv)))

; The underlying embedded relation of a quiver is an inclusion function
(defn underlying-embedded-relation
  [quiv]

  (inclusion-function
    (set (underlying-relation quiv))
    (complete-relation (morphisms quiv))))

; Visualisation
(defmethod visualize Quiver
  [quiv] (visualize (underlying-multirelation quiv)))

; Products and coproducts in the topos of quivers
(defn quiver-product
  [& quivers]

  (Quiver.
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
        coll))))

(defn quiver-coproduct
  [& quivers]

  (Quiver.
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (fn [[i v]]
      (list i (source-element (nth quivers i) v)))
    (fn [[i v]]
      (list i (target-element (nth quivers i) v)))))

(defmethod product Quiver
  [& args]

  (apply quiver-product args))

(defmethod coproduct Quiver
  [& args]

  (apply quiver-coproduct args))

; Transposition of quivers
(defmethod dual Quiver
  [^Quiver quiv]

  (Quiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)))

; Equalizers and coequalizers in the topos of quivers
(defn quiver-equalizer
  [quiver]

  (set
    (filter
      (fn [i]
        (= (source-element quiver i)
           (target-element quiver i)))
      (morphisms quiver))))

(defn quiver-coequalizer
  [quiver]

  (coequalizer
    (source-function quiver)
    (target-function quiver)))

(defn quiver-equalizer-function
  [quiver]

  (equalizer-function
    (source-function quiver)
    (target-function quiver)))

(defn quiver-coequalizer-function
  [quiver]

  (coequalizer-function
    (source-function quiver)
    (target-function quiver)))

; Objects theory
(defn predecessor-objects
  [quiv object]

  (set
    (for [i (morphisms quiv)
          :when (= (target-element quiv i) object)
          :let [source (source-element quiv i)]]
      source)))

(defn proper-predecessor-objects
  [quiv a]

  (disj (set (predecessor-objects quiv a)) a))

(defn quiver-vertex-in-degree
  [quiv a]

  (count (predecessor-objects quiv a)))

(defn quiver-vertex-proper-in-degree
  [quiv a]

  (count (proper-predecessor-objects quiv a)))

(defn successor-objects
  [quiv object]

  (set
    (for [i (morphisms quiv)
          :when (= (source-element quiv i) object)
          :let [target (target-element quiv i)]]
      target)))

(defn proper-successor-objects
  [quiv a]

  (disj (set (successor-objects quiv a)) a))

(defn quiver-vertex-out-degree
  [quiv a]

  (count (successor-objects quiv a)))

(defn quiver-vertex-proper-out-degree
  [quiv a]

  (count (proper-successor-objects quiv a)))

; Get all objects not appearing as the source of an edge
(defn missing-sources
  [quiver]

  (difference
    (set (objects quiver))
    (set
      (map
        (fn [i]
          (source-element quiver i))
        (morphisms quiver)))))

(defn missing-targets
  [quiver]

  (difference
    (set (objects quiver))
    (set
      (map
        (fn [i]
          (target-element quiver i))
        (morphisms quiver)))))

(defn missing-objects
  [quiver]

  (intersection
    (missing-sources quiver)
    (missing-targets quiver)))

; Morphisms theory
(defn quiver-loops
  [quiver]

  (set
    (filter
      (fn [i]
        (equal-seq? (transition quiver i)))
      (first-set quiver))))

(defn quiver-nonloops
  [quiver]

  (set
    (filter
      (fn [i]
        (distinct-seq? (transition quiver i)))
      (first-set quiver))))

; Objects connectivity
(defn quiver-weak-connectivity
  [quiver]

  (weak-connectivity (underlying-relation quiver)))

(defn quiver-strong-connectivity
  [quiver]

  (strong-connectivity (underlying-relation quiver)))

; Composability relations
; The composability relation of a compositional quiver such as a semigroupoid
; or a category appears as the domain of the composition function of the
; compositional quiver. Therefore, its computation is one of the most basic
; constructs of category theory.
(defn composable-elements?
  [quiver a b]

  (= (target-element quiver b)
     (source-element quiver a)))

(defn bidirectionally-composable-elements?
  [category a b]

  (and
    (= (source-element category a) (target-element category b))
    (= (target-element category a) (source-element category b))))

(defn composability-relation
  [quiver]

  (let [morphisms (morphisms quiver)]
    (->SeqableRelation
      morphisms
      (fn [[a b]]
        (composable-elements? quiver a b))
      {})))

(defn composability-quiver
  [quiver]

  (relational-quiver
    (morphisms quiver)
    (composability-relation quiver)))

; Composition paths
; A composition path is a generalize of a compositional pair to any number of elements
(defn composition-path?
  [quiver coll]

  (or
    (empty? coll)
    (every?
      (fn [i]
        (composable-elements? quiver (nth coll i) (nth coll (inc i))))
      (range (dec (count coll))))))

; Source equality relations
(defn source-equal-elements?
  [quiver a b]

  (= (source-element quiver a)
     (source-element quiver b)))

(defn source-equivalence-relation
  [quiver]

  (let [morphisms (morphisms quiver)]
    (->SeqableRelation
      morphisms
      (fn [[a b]]
        (source-equal-elements? quiver a b))
      {})))

(defn source-equivalence-quiver
  [quiver]

  (relational-quiver
    (morphisms quiver)
    (source-equivalence-quiver quiver)))

; Get the equivalence classes of the source equality relation
; These are all morphisms that start at a given object of a quiver
(defn under-morphisms
  [quiv a]

  (set
    (filter
      (fn [morphism]
        (= (source-element quiv morphism) a))
      (morphisms quiv))))

(defn quiver-edge-out-degree
  [quiv a]

  (count (under-morphisms quiv a)))

; Target equality relations
(defn target-equal-elements?
  [quiver a b]

  (= (target-element quiver a)
     (target-element quiver b)))

(defn target-equivalence-relation
  [quiver]

  (let [morphisms (morphisms quiver)]
    (->SeqableRelation
      morphisms
      (fn [[a b]]
        (target-equal-elements? quiver a b))
      {})))

(defn target-equivalence-quiver
  [quiver]

  (relational-quiver
    (morphisms quiver)
    (target-equivalence-relation quiver)))

; Get equivalence classes of the target equal relation
; These are all morphisms that target a given object in a quiver
(defn over-morphisms
  [quiv a]

  (set
    (filter
      (fn [morphism]
        (= (target-element quiv morphism) a))
      (morphisms quiv))))

(defn quiver-edge-in-degree
  [quiv a]

  (count (over-morphisms quiv a)))

; Check if elements of a quiver are instead parallel for use in constructing globular sets
(defn parallel-elements?
  [quiver a b]

  (and
    (= (source-element quiver a) (source-element quiver b))
    (= (target-element quiver a) (target-element quiver b))))

(defn parallelism-relation
  [quiver]

  (let [morphisms (morphisms quiver)]
    (->SeqableRelation
      morphisms
      (fn [[a b]]
        (parallel-elements? quiver a b))
      {})))

(defn parallelism-quiver
  [quiver]

  (relational-quiver
    (morphisms quiver)
    (parallelism-relation quiver)))

; Equivalence classes of the parallelism relation
; These are precisely the hom classes of the quiver.
(defn quiver-hom-class
  [quiv a b]

  (let [arrows (morphisms quiv)]
    (if (seqable-universal? arrows)
      (seqable-filter
        (fn [e]
          (and
            (= (source-element quiv e) a)
            (= (target-element quiv e) b)))
        arrows)
      (fn [e]
        (and
          (= (source-element quiv e) a)
          (= (target-element quiv e) b))))))

(defn quiver-hom-cardinality
  [quiv a b]

  (count (quiver-hom-class quiv a b)))

; Images and inverse images in the topos Sets^{T_2^*}
; Quivers are in a unique position to have generalized versions of the images of functions,
; as they are simply parallel collections of functions. So these same function operations
; are generalized to quivers, and the topos theoretic process by which we generalized from
; set images to partition images can also be applied to quivers as well. Then with these new
; operations, we can generate subobject and congruence lattices for quivers as well.
(defn quiver-set-image
  [quiver coll]

  (union
    (set-image (source-function quiver) coll)
    (set-image (target-function quiver) coll)))

(defn quiver-set-inverse-image
  [quiver coll]

  (set
    (filter
      (fn [e]
        (and
          (contains? coll (source-element quiver e))
          (contains? coll (target-element quiver e))))
      (morphisms quiver))))

(defn quiver-partition-image
  [quiver partition]

  (join-set-partitions
    (partition-image (source-function quiver) partition)
    (partition-image (target-function quiver) partition)))

(defn quiver-partition-inverse-image
  [quiver partition]

  (meet-set-partitions
    (partition-inverse-image (source-function quiver) partition)
    (partition-inverse-image (target-function quiver) partition)))

; Set images for quivers
(defmethod image
  [:locus.quiver.base.core.protocols/quiver :locus.base.logic.core.set/universal]
  [quiver coll]

  (quiver-set-image quiver coll))

(defmethod inverse-image
  [:locus.quiver.base.core.protocols/quiver :locus.base.logic.core.set/universal]
  [quiver coll]

  (quiver-set-inverse-image quiver coll))

; Subobjects of quivers
(defn subquiver
  [q new-edges new-vertices]

  (Quiver.
    new-edges
    new-vertices
    (source-fn q)
    (target-fn q)))

; Wide and full subquivers
; A full subquiver is defined by taking a subset of the vertices of the quiver, and then having
; the result be the largest possible subquiver determined by the set inverse image. A wide
; subquiver is defined by taking a subset of the edges of the quiver and then using
; restriction on them.
(defn full-subquiver
  [quiver new-vertices]

  (Quiver.
    (quiver-set-inverse-image quiver new-vertices)
    new-vertices
    (source-fn quiver)
    (target-fn quiver)))

(defn wide-subquiver
  [quiver new-edges]

  (Quiver.
    new-edges
    (objects quiver)
    (source-fn quiver)
    (target-fn quiver)))

; Subobjects in the topos of quivers
(defn subquiver?
  [quiver new-in new-out]

  (superset?
    (list
      (quiver-set-image quiver new-in)
      new-out)))

(defn subquiver-closure
  [quiv new-in new-out]

  (list
    new-in
    (union new-out (quiver-set-image quiv new-in))))

; Enumeration theory of subalgebras of quivers
(defn possible-subquivers-by-in-set
  [quiv in-set]

  (let [minimal-out-set (quiver-set-image quiv in-set)
        possible-out-additions (set
                                 (difference
                                   (objects quiv)
                                   minimal-out-set))]
    (map
      (fn [out-additions]
        (list in-set (union minimal-out-set out-additions)))
      (power-set possible-out-additions))))

(defn subquivers
  [quiver]

  (set
    (mapcat
      (fn [in-set]
        (possible-subquivers-by-in-set quiver in-set))
      (power-set (morphisms quiver)))))

; Relations related to the class of subquivers
(defn subquivers-relation
  [quiv]

  (SeqableRelation.
    (subquivers quiv)
    (fn [[[a b] [c d]]]
      (and
        (superset? (list a c))
        (superset? (list b d))))
    {}))

(defn quiver-covering-additions
  [quiv in-set out-set]

  [(set
     (filter
       (fn [edge]
         (and
           (contains? out-set (source-element quiv edge))
           (contains? out-set (target-element quiv edge))))
       (difference (.edges quiv) in-set)))
   (difference (.vertices quiv) out-set)])

(defn covering-subquivers
  [func in-set out-set]

  (let [[inputs-additions outputs-additions] (quiver-covering-additions func in-set out-set)]
    (union
      (set
        (map
          (fn [i]
            [(conj in-set i) out-set])
          inputs-additions))
      (set
        (map
          (fn [i]
            [in-set (conj out-set i)])
          outputs-additions)))))

(defn subquivers-covering
  [quiv]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (covering-subquivers quiv in-set out-set)))
      (subquivers quiv))))

; Quotient quivers
(defn quotient-quiver
  [q in-partition out-partition]

  (Quiver.
    in-partition
    out-partition
    (fn [part]
      (projection out-partition (source-element q (first part))))
    (fn [part]
      (projection out-partition (target-element q (first part))))))

; Quiver congruences
(defn quiver-congruence?
  [quiv in-partition out-partition]

  (set-superpartition?
    (list
      (quiver-partition-image quiv in-partition)
      out-partition)))

(defn quiver-congruence-closure
  [quiv new-in new-out]

  (list
    new-in
    (join-set-partitions
      new-out
      (quiver-partition-image quiv new-in))))

; Methods for computing congruence lattices of quivers
(defn possible-quiver-congruences-by-in-partition
  [quiver in-partition]

  (let [current-image-partition (quiver-partition-image quiver in-partition)]
    (map
      (fn [out-partition]
        (list in-partition out-partition))
      (set-partition-coarsifications current-image-partition))))

(defn quiver-congruences
  [quiver]

  (set
    (mapcat
      (fn [in-partition]
        (possible-quiver-congruences-by-in-partition quiver in-partition))
      (enumerate-set-partitions (morphisms quiver)))))

; Relations related to the class of all quiver congruences
(defn quiver-covering-congruences
  [quiver in-partition out-partition]

  (union
    (set
      (map
        (fn [new-out-partition]
          (list in-partition new-out-partition))
        (direct-set-partition-coarsifications out-partition)))
    (set
      (for [i (direct-set-partition-coarsifications in-partition)
            :when (set-superpartition?
                    (list (quiver-partition-image quiver i) out-partition))]
        (list i out-partition)))))

(defn quiver-congruences-covering
  [quiver]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list [in-partition out-partition] [new-in-partition new-out-partition]))
          (quiver-covering-congruences quiver in-partition out-partition)))
      (quiver-congruences quiver))))

(defn quiver-congruences-relation
  [quiv]

  (SeqableRelation.
    (quiver-congruences quiv)
    (fn [[[a b] [c d]]]
      (and
        (set-superpartition? (list a c))
        (set-superpartition? (list b d))))
    {}))

; Get a together total congruence by removing all missing members
(defn together-total-subalgebra
  [quiver]

  (list
    (morphisms quiver)
    (difference (objects quiver) (missing-objects quiver))))

(defn together-total-subalgebra-by
  [quiver input-set]

  (list
    input-set
    (quiver-set-image quiver input-set)))

(defn together-total-subalgebras
  [quiver]

  (set
    (map
      (fn [morphism-set]
        (together-total-subalgebra-by morphism-set))
      (power-set (morphisms quiver)))))

(defn together-total-subquiver
  [quiver]

  (subquiver
    quiver
    (morphisms quiver)
    (difference (objects quiver) (missing-objects quiver))))

; The thin congruence naturally associated with any quiver
(defn thin-congruence
  [quiver]

  (list
    (pn
      (partial parallel-elements? quiver)
      (morphisms quiver))
    (set
      (map
        (fn [i]
          #{i})
        (objects quiver)))))

(defn thin-congruence-by-object-partition
  [quiver object-partition]

  (let [func (partition->projection object-partition)
        morphism-partition (pn
                             (fn [a b]
                               (let [[a1 a2] (transition quiver a)
                                     [b1 b2] (transition quiver b)]
                                 (and
                                   (= (func a1) (func b1))
                                   (= (func a2) (func b2)))))
                             (morphisms quiver))]
    (list morphism-partition object-partition)))

(defn thin-congruences
  [quiver]

  (set
    (map
      (fn [object-partition]
        (thin-congruence-by-object-partition quiver object-partition))
      (enumerate-set-partitions (objects quiver)))))

(defn thin-quotient
  [quiver]

  (relational-quiver (underlying-relation quiver)))

; Reflexive and irreflexive components form wide subquivers
(defn coreflexive-subquiver
  [quiver]

  (wide-subquiver
    quiver
    (quiver-loops quiver)))

(defn irreflexive-subquiver
  [quiver]

  (wide-subquiver
    quiver
    (quiver-nonloops quiver)))

; Full quotients of quivers
(defn full-quotient-quiver
  [quiver in-partition]

  (quotient-quiver quiver in-partition (quiver-partition-image quiver in-partition)))

; Ontology of quivers
(defmulti quiver? type)

(defmethod quiver? :locus.quiver.base.core.protocols/quiver
  [quiv] true)

(defmethod quiver? :default
  [quiv] false)

; Classification of quivers by number of objects
(defn two-object-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (= (count (objects quiv)) 2)))

(defn three-object-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (= (count (objects quiv)) 3)))

(defn four-object-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (= (count (objects quiv)) 4)))

; Source and target surjective quivers
(defn together-total-quiver?
  [quiv]

  (= (objects quiv)
     (apply union (map set (underlying-relation quiv)))))

(defn left-total-quiver?
  [quiv]

  (= (objects quiv)
     (set (map first (underlying-multirelation quiv)))))

(defn right-total-quiver?
  [quiv]

  (= (objects quiv)
     (set (map second (underlying-multirelation quiv)))))

(def bitotal-quiver?
  (intersection
    left-total-quiver?
    right-total-quiver?))

; Source injective quivers are like functions
(defn source-injective-quiver?
  [quiver]

  (and
    (quiver? quiver)
    (let [edges (seq (morphisms quiver))]
      (distinct-seq?
        (map
          (fn [i]
            (source-element quiver i))
          edges)))))

(defn target-injective-quiver?
  [quiver]

  (and
    (quiver? quiver)
    (let [edges (seq (morphisms quiver))]
      (distinct-seq?
        (map
          (fn [i]
            (target-element quiver i))
          edges)))))

(defn thin-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (universal? (underlying-multirelation quiv))))

; Together total thin quivers are also called relational quivers
(defn relational-quiver?
  [quiv]

  (and
    (together-total-quiver? quiv)
    (thin-quiver? quiv)))

(defn left-total-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (left-total-quiver? quiv)))

(defn right-total-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (right-total-thin-quiver? quiv)))

(defn bitotal-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (bitotal-quiver? quiv)))

; Endotrivial quivers are quivers that are thin over all equal hom objects, so that in the hom
; class Hom(A,A) for each object A there is no more than one object.
(defn endotrivial-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (every?
      (fn [obj]
        (<= (quiver-hom-cardinality quiv obj obj) 1))
      (objects quiv))))

; Double arrow free quivers are quivers that are thin over all distinct hom objects, so that in
; them hom class Hom(A,B) for A not equal to b there is no more than one object.
(defn double-arrow-free-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (let [coll (multiplicities-map (underlying-multirelation quiv))]
      (every?
        (fn [pair]
          (let [[a b] pair]
            (or
              (= a b)
              (<= (get coll pair) 1))))
        (keys coll)))))

; A compositionally thin endotrivial quiver is one for which we can say that for each pair
; of non-endomorphisms f:A -> B and g: B -> C there is no more than one element in the hom
; class A -> C. In such a case, these quivers can be uniquely converted in to categories.
(defn compositionally-thin-endotrivial-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (every?
      (fn [[edge1 edge2]]
        (or
          (= (source-element quiv edge1) (target-element quiv edge1))
          (= (source-element quiv edge2) (target-element quiv edge2))
          (let [new-class (quiver-hom-class quiv (source-element quiv edge2) (target-element quiv edge1))]
            (<= (count new-class) 1))))
      (composability-relation quiv))))

; Every irreflexive quiver is endotrivial
(defn irreflexive-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (empty? (quiver-loops quiv))))

(def irreflexive-thin-quiver?
  (intersection
    irreflexive-quiver?
    thin-quiver?))

; Special classes of quivers by their types of elements
(defn coreflexive-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (empty? (quiver-nonloops quiv))))

(defn coreflexive-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

; Further classes of thin quivers
(defn symmetric-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (symmetric-binary-relation? (underlying-relation quiv))))

(defn reflexive-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (reflexive? (underlying-relation quiv))))

(defn symmetric-reflexive-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (dependency-relation? (underlying-relation quiv))))

(defn symmetric-irreflexive-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (independency-relation? (underlying-relation quiv))))

(defn complete-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (complete-relation? (underlying-relation quiv))))

; Connectivity classes for more general quivers
(defn weakly-connected-ouiver?
  [quiv]

  (and
    (quiver? quiv)
    (weakly-connected-relation? (underlying-relation quiv))))

(defn strongly-connected-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (strongly-connected-relation? (underlying-relation quiv))))

; Connectivity classes of thin quivers
(defn strongly-connected-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (strongly-connected-relation? (underlying-relation quiv))))

(defn weakly-connected-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (weakly-connected-relation? (underlying-relation quiv))))

; Directed acyclic quivers
(defn directed-acyclic-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (acyclic-relation? (underlying-relation quiv))))

; Antisymmetric quivers
(defn antisymmetric-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (antisymmetric? (underlying-relation quiv))))

(defn asymmetric-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (asymmetric? (underlying-relation quiv))))

; Extra classes of quivers
(defn preposetal-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (preorder? (underlying-relation quiv))))

(defn posetal-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (partial-order? (underlying-relation quiv))))

(defn tosetal-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (total-order? (underlying-relation quiv))))

; Specific classes of quivers formed by binary relations
(defn equivalence-quiver?
  [quiv]

  (and
    (reflexive-thin-quiver? quiv)
    (equivalence-relation? (underlying-relation quiv))))

(defn lattice-quiver?
  [quiv]

  (and
    (reflexive-thin-quiver? quiv)
    (lattice-relation? (underlying-relation quiv))))
