(ns locus.elementary.quiver.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all])
  (:import [locus.elementary.function.core.object SetFunction]
           [locus.elementary.relation.binary.sr SeqableRelation]))

; Objects in the topos Sets^{T^2_*}
; Let T_2^* be the totally ordered category with two objects and four morphisms.
; Then this category is the index category of a topos: the topos of quivers
; Sets^(T_2^*). In this file, we implement the routines for dealing
; with elements of this fundamental topos.

; A quiver should implement diset and the structured quiver protocol
(defprotocol StructuredQuiver
  "Let Quiv be the category of quivers. Then we can define a category C over Quiv by a forgetful functor,
  f : C->Quiv. This protocol defines methods for handling objects such categories with reference to their
  forgetful functors to the topos of quivers."

  (underlying-quiver [this]
    "Get the output quiver of the mapping to the topos of quivers.")
  (source-fn [this]
    "The source function of the structured quiver returned as a Clojure IFn.")
  (target-fn [this]
    "The target function of the structured quiver returned as a Clojure IFn.")
  (transition [this obj]
    "This returns for a morphism f:A->B the ordered pair (A,B) called its transition."))

; An ad hoc hierarchy of quivers
(derive ::quiver :locus.elementary.function.core.protocols/structured-quiver)
(derive ::thin-quiver ::quiver)

; A default implementation of the quiver protocol
(defrecord Quiver [edges vertices source-function target-function]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] this)
  (source-fn [this] source-function)
  (target-fn [this] target-function)
  (transition [this obj] (list (source-function obj) (target-function obj))))

(derive Quiver ::quiver)

; These are very useful shorthands
(defn source-element
  [quiv elem]

  ((source-fn quiv) elem))

(defn target-element
  [quiv elem]

  ((target-fn quiv) elem))

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

; Utilities for constructing quivers
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

; These are useful constructors for quivers
(defmulti to-quiver type)

(defmethod to-quiver SetFunction
  [func]

  (Quiver.
    (underlying-relation func)
    (union (inputs func) (outputs func))
    first
    second))

(defmethod to-quiver clojure.lang.PersistentArrayMap
  [coll]

  (Quiver.
    (set (map seq coll))
    (union (set (keys coll)) (set (vals coll)))
    first
    second))

(defmethod to-quiver :default
  [rel]

  (cond
    (universal? rel) (relational-quiver rel)
    (multiset? rel) (multirelational-quiver rel)
    :else (underlying-quiver rel)))

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

; Quiver utility functions
(defn quiver-order
  [quiv]

  (count (objects quiv)))

(defn quiver-size
  [quiv]

  (count (morphisms quiv)))

; Visualisation
(defmethod visualize Quiver
  [quiv] (visualize (underlying-multirelation quiv)))

; Transposition of quivers
(defmethod dual Quiver
  [^Quiver quiv]

  (Quiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)))

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

; Hom classes of quivers
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

; Get all over morphisms of a structured quiver object
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

; Get all under morphisms of a structured quiver object
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

; Get the predecessor and successor objects by the over and under morphisms
(defn predecessor-objects
  [quiv a]

  (let [morphisms (over-morphisms quiv a)]
    (map
      (fn [morphism]
        (source-element quiv morphism))
      morphisms)))

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
  [quiv a]

  (let [morphisms (under-morphisms quiv a)]
    (map
      (fn [morphism]
        (target-element quiv morphism))
      morphisms)))

(defn proper-successor-objects
  [quiv a]

  (disj (set (successor-objects quiv a)) a))

(defn quiver-vertex-out-degree
  [quiv a]

  (count (successor-objects quiv a)))

(defn quiver-vertex-proper-out-degree
  [quiv a]

  (count (proper-successor-objects quiv a)))

; The underlying embedded relation of a quiver is an inclusion function
(defn underlying-embedded-relation
  [quiv]

  (inclusion-function
    (set (underlying-multirelation quiv))
    (complete-relation (morphisms quiv))))

; Source and target functions
(defn source-function
  [q]

  (SetFunction.
    (morphisms q)
    (objects q)
    (source-fn q)))

(defn target-function
  [q]

  (SetFunction.
    (morphisms q)
    (objects q)
    (target-fn q)))

; Subobjects and quotients of quivers
(defn subquiver
  [q new-edges new-vertices]

  (Quiver.
    new-edges
    new-vertices
    (source-fn q)
    (target-fn q)))

(defn quotient-quiver
  [q edge-partition vertex-partition]

  (Quiver.
    edge-partition
    vertex-partition
    (fn [part]
      (projection edge-partition (source-element q (first part))))
    (fn [part]
      (projection edge-partition (target-element q (first part))))))

; Induced subquiver
(defn full-subquiver
  [quiver new-vertices]

  (Quiver.
    (set
      (filter
        (fn [e]
          (and
            (contains? new-vertices (source-element quiver e))
            (contains? new-vertices (target-element quiver e))))
        (.edges quiver)))
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

; We need some ability to deal with issues of subquivers
(defn subquiver?
  [q new-in new-out]

  (superset?
    (list
      (union
        (set-image (source-function q) new-in)
        (set-image (target-function q) new-in))
      new-out)))

(defn subquiver-closure
  [quiv new-in new-out]

  (list new-in
        (union
          new-out
          (set-image (source-function quiv) new-in)
          (set-image (target-function quiv) new-in))))

(defn subquivers
  [quiv]

  (set
    (filter
      (fn [[a b]]
        (subquiver? quiv a b))
      (cartesian-product (power-set (morphisms quiv)) (power-set (objects quiv))))))

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
  [quiv new-edges new-vertices]

  [(set
     (filter
       (fn [edge]
         (and
           (contains? new-vertices (source-element quiv edge))
           (contains? new-vertices (target-element quiv edge))))
       (difference (.edges quiv) new-edges)))
   (difference (.vertices quiv) new-vertices)])

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

; Quiver congruences
(defn quiver-congruence?
  [quiv in-partition out-partition]

  (set-superpartition?
    (list
      (join-set-partitions
        (partition-image (source-function quiv) in-partition)
        (partition-image (target-function quiv) in-partition))
      out-partition)))

(defn quiver-congruence-closure
  [quiv new-in new-out]

  (list new-in
        (join-set-partitions
          new-out
          (partition-image (source-function quiv) new-in)
          (partition-image (target-function quiv) new-out))))

(defn quiver-congruences
  [quiv]

  (set
    (filter
      (fn [[a b]]
        (quiver-congruence? quiv a b))
      (cartesian-product
        (set-partitions (morphisms quiv))
        (set-partitions (objects quiv))))))

(defn quiver-congruences-relation
  [quiv]

  (SeqableRelation.
    (quiver-congruences quiv)
    (fn [[[a b] [c d]]]
      (and
        (set-superpartition? (list a c))
        (set-superpartition? (list b d))))
    {}))

; Quiver connectivity
(defn quiver-weak-connectivity
  [quiver]

  (weak-connectivity (underlying-relation quiver)))

(defn quiver-strong-connectivity
  [quiver]

  (strong-connectivity (underlying-relation quiver)))

; Get the loops and non-loops of a quiver
(defn quiver-loops
  [quiver]

  (filter
    (fn [i]
      (equal-seq? (transition quiver i)))
    (first-set quiver)))

(defn quiver-nonloops
  [quiver]

  (filter
    (fn [i]
      (distinct-seq? (transition quiver i)))
    (first-set quiver)))

; Ontology of quivers
(defmulti quiver? type)

(defmethod quiver? ::quiver
  [quiv] true)

(defmethod quiver? :default
  [quiv] false)

(defn coreflexive-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (empty? (quiver-nonloops quiv))))

(defn irreflexive-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (empty? (quiver-loops quiv))))

; Totality conditions
(defn left-total-quiver?
  [quiv]

  (= (.vertices quiv)
     (set (map first (underlying-multirelation quiv)))))

(defn right-total-quiver?
  [quiv]

  (= (.vertices quiv)
     (set (map second (underlying-multirelation quiv)))))

(def total-quiver?
  (intersection
    left-total-quiver?
    right-total-quiver?))

; Ontology of thin quivers
(defn thin-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (universal? (underlying-multirelation quiv))))

(defn coreflexive-thin-quiver?
  [quiv]

  (and
    (thin-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

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

(def irreflexive-thin-quiver?
  (intersection
    irreflexive-quiver?
    thin-quiver?))

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

; Antisymmetric quivers
(defn antisymmetric-quiver?
  [quiv]

  (and
    (quiver? quiv)
    (antisymmetric? (underlying-relation quiv))))

(defn antisymmetric-quiver?
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
