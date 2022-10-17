(ns locus.elementary.quiver.dependency.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection restrict-partition]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all])
  (:import [locus.base.function.core.object SetFunction]
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
(deftype DependencyQuiver [edges vertices source-function target-function id inv]
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

(derive ::dependency-quiver :locus.elementary.copresheaf.core.protocols/structured-dependency-quiver)
(derive ::thin-dependency-quiver ::dependency-quiver)
(derive DependencyQuiver ::dependency-quiver)

; Inverse functions in the topos of dependency quivers
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

; Singular dependency quivers
(defn singular-dependency-quiver
  [morphisms obj id inv]

  (->DependencyQuiver
    morphisms
    #{obj}
    (constantly obj)
    (constantly obj)
    id
    inv))

; Relational dependency quivers
(defn relational-dependency-quiver
  ([rel]
   (relational-dependency-quiver (vertices rel) rel))
  ([coll rel]
   (->DependencyQuiver
     rel
     coll
     first
     second
     (fn [i]
       (list i i))
     reverse)))

; Create dependency quivers from set systems
(defn familial-dependency-quiver
  [coll]

  (relational-dependency-quiver (symmetric-binary-relation coll)))

; Conversion routines
(defmulti to-dependency-quiver type)

(defmethod to-dependency-quiver DependencyQuiver
  [quiver] quiver)

(defmethod to-dependency-quiver :locus.base.logic.core.set/universal
  [rel] (relational-dependency-quiver rel))

(defmethod to-dependency-quiver :default
  [obj] (underlying-dependency-quiver obj))

; Create dependency quivers by sets of morphisms and objects
(defn as-dependency-quiver
  [morphisms objects]

  (->DependencyQuiver
    morphisms
    objects
    source-object
    target-object
    identity-morphism
    inv))

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

; Underlying multirelations of dependency quivers
(defmethod underlying-multirelation DependencyQuiver
  [quiver]

  (multiset
    (map
      (fn [e]
        (transition quiver e))
      (morphisms quiver))))

(defmethod underlying-relation DependencyQuiver
  [quiver] (set (underlying-multirelation quiver)))

; Visualisation of dependency quivers
(defmethod visualize DependencyQuiver
  [quiver]

  (visualize (underlying-multifamily quiver)))

; Dependency subquivers
(defn dependency-subquiver
  [quiver new-in new-out]

  (DependencyQuiver.
    new-in
    new-out
    (source-fn quiver)
    (target-fn quiver)
    (.id quiver)
    (.inv quiver)))

(defn wide-dependency-subquiver
  [quiver new-morphisms]

  (dependency-subquiver
    quiver
    new-morphisms
    (objects quiver)))

(defn full-dependency-subquiver
  [quiver new-objects]

  (dependency-subquiver
    quiver
    (quiver-set-inverse-image quiver new-objects)
    new-objects))

; Dependency subquivers as a special class of quivers
(defn dependency-subquiver?
  [quiv new-edges new-vertices]

  (and
    (subquiver? quiv new-edges new-vertices)
    (inversion-closed-subset? quiv new-edges)
    (superset? (list (identity-morphism-of quiv new-vertices) new-edges))))

; Enumeration theory for dependency subquivers
(defn dependency-subquivers-by-object-set
  [quiv object-set]

  (let [object-set-identities (identity-morphisms-of quiv object-set)
        possible-morphisms (difference
                             (quiver-set-inverse-image quiv object-set)
                             object-set-identities)
        possible-morphism-inversion-classes (inversion-equivalence-of quiv possible-morphisms)]
    (map
      (fn [inversion-classes]
        (let [all-elements (apply union inversion-classes)
              new-morphism-set (union all-elements object-set-identities)]
          (list new-morphism-set object-set)))
      (power-set possible-morphism-inversion-classes))))

(defn dependency-subquivers
  [quiv]

  (mapcat
    (fn [object-set]
      (dependency-subquivers-by-object-set quiv object-set))
    (power-set (objects quiv))))

; We can now try to find the covering relation for the distributive subobject lattice of
; subobjects in the topos of dependency quivers.
(defn covering-dependency-subquivers
  [quiv in-set out-set]

  (concat
    (map
      (fn [new-object]
        (list
          (conj in-set (identity-morphism-of quiv new-object))
          (conj out-set new-object)))
      (difference (objects quiv) out-set))
    (let [possible-morphisms (difference
                               (quiver-set-inverse-image quiv out-set)
                               in-set)
          possible-inversion-classes (inversion-equivalence-of quiv possible-morphisms)]
      (map
        (fn [inversion-class]
          (list
            (union in-set inversion-class)
            out-set))
        possible-inversion-classes))))

(defn dependency-quivers-covering
  [quiv]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (covering-dependency-subquivers quiv in-set out-set)))
      (dependency-subquivers quiv))))

; Quotients in the topos of dependency quivers
(defn quotient-dependency-quiver
  [quiver in-partition out-partition]

  (DependencyQuiver.
    in-partition
    out-partition
    (fn [part]
      (projection out-partition (source-element quiver (first part))))
    (fn [part]
      (projection out-partition (target-element quiver (first part))))
    (fn [obj]
      (projection in-partition (identity-morphism-of quiver obj)))
    (fn [part]
      (projection in-partition (invert-morphism quiver (first part))))))

; Congruences of dependency quivers
(defn dependency-quiver-congruence?
  [quiver in-partition out-partition]

  (and
    (unital-quiver-congruence? quiver in-partition out-partition)
    (inversion-congruence? quiver in-partition)))

; Enumeration theory for congruences of dependency quivers
(defn dependency-quiver-morphism-partitions-by-object-partition
  [quiver object-partition]

  (let [morphism-partitions (unital-quiver-morphism-partitions-by-object-partition
                              quiver
                              object-partition)]
    (filter
      (fn [morphism-partition]
        (inversion-congruence? quiver morphism-partition))
      morphism-partitions)))

(defn dependency-quiver-congruences-by-object-partition
  [quiver object-partition]

  (map
    (fn [morphism-partition]
      (list morphism-partition object-partition))
    (dependency-quiver-morphism-partitions-by-object-partition quiver object-partition)))

(defn dependency-quiver-congruences
  [quiver]

  (set
    (mapcat
      (fn [object-partition]
        (dependency-quiver-congruences-by-object-partition quiver object-partition))
      (enumerate-set-partitions (objects quiver)))))

; Relations on congruences of dependency quivers
(defn dependency-quiver-covering-congruences
  [quiv in-partition out-partition]

  (union
    (set
      (map
        (fn [new-out-partition]
          (let [identity-induced-partition (minimal-morphism-partition-by-object-partition
                                             quiv
                                             new-out-partition)
                new-in-partition (join-set-partitions identity-induced-partition in-partition)]
            (list new-in-partition new-out-partition)))
        (direct-set-partition-coarsifications out-partition)))
    (object-preserving-permutable-quiver-covering-congruences quiv in-partition out-partition)))

(defn dependency-quiver-congruences-covering
  [quiver]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list [in-partition out-partition] [new-in-partition new-out-partition]))
          (dependency-quiver-covering-congruences quiver in-partition out-partition)))
      (dependency-quiver-congruences quiver))))

; Ontology of dependency quivers
(defmulti dependency-quiver? type)

(defmethod dependency-quiver? ::dependency-quiver
  [quiver] true)

(defmethod dependency-quiver? :default
  [quiver] false)

(defn thin-dependency-quiver?
  [quiv]

  (and
    (dependency-quiver? quiv)
    (universal? (underlying-multirelation quiv))))

(defn coreflexive-dependency-quiver?
  [quiv]

  (and
    (dependency-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

(defn coreflexive-thin-dependency-quiver?
  [quiv]

  (and
    (thin-dependency-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

