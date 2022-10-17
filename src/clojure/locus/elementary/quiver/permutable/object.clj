(ns locus.elementary.quiver.permutable.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [restrict-partition projection partitionize-family]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import [locus.base.function.core.object SetFunction]
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
(deftype PermutableQuiver [edges vertices source-function target-function inv]
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

(derive ::permutable-quiver :locus.elementary.copresheaf.core.protocols/structured-permutable-quiver)
(derive ::thin-permutable-quiver ::permutable-quiver)
(derive PermutableQuiver ::permutable-quiver)

; Get the inverse function from a permutable quiver
(defmethod inverse-function PermutableQuiver
  [^PermutableQuiver quiv]

  (->SetFunction
    (morphisms quiv)
    (morphisms quiv)
    (fn [edge]
      (invert-morphism quiv edge))))

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

; Create a singular permutable quiver
(defn singular-permutable-quiver
  [morphisms obj inv]

  (->PermutableQuiver
    morphisms
    #{obj}
    (constantly obj)
    (constantly obj)
    inv))

; Permutable quivers from symmetric relations
(defn relational-permutable-quiver
  ([rel]
   (relational-permutable-quiver (vertices rel) rel))
  ([coll rel]
   (PermutableQuiver. rel coll first second reverse)))

(defn multirelational-permutable-quiver
  ([rel]
   (multirelational-permutable-quiver (vertices rel) rel))
  ([coll rel]
   (PermutableQuiver.
     (binary-multirelation->tagged-ternary-relation rel)
     coll
     first
     second
     (fn [[a b n]]
       (list b a n)))))

; Conversions for set systems and multiset systems
(defn familial-permutable-quiver
  [family]

  (relational-permutable-quiver
    (symmetric-binary-relation family)))

(defn multifamilial-permutable-quiver
  [coll]

  (multirelational-permutable-quiver
    (symmetric-binary-multirelation coll)))

; A multimethod for conversions to permutable quivers
(defmulti to-permutable-quiver type)

(defmethod to-permutable-quiver PermutableQuiver
  [quiv] quiv)

(defmethod to-permutable-quiver :locus.base.logic.core.set/universal
  [coll]

  (relational-permutable-quiver coll))

(defmethod to-permutable-quiver :default
  [obj]

  (underlying-permutable-quiver obj))

; Create permutable quivers by elements
(defn as-permutable-quiver
  [morphisms objects]

  (->PermutableQuiver
    morphisms
    objects
    source-object
    target-object
    inv))

; Underlying relations for permutable quivers
(defmethod underlying-multirelation PermutableQuiver
  [^PermutableQuiver quiver]

  (multiset
    (map
      (fn [e]
        (transition quiver e))
      (morphisms quiver))))

(defmethod underlying-relation PermutableQuiver
  [^PermutableQuiver quiver]

  (set (underlying-multirelation quiver)))

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

; Duals of permutable quivers
(defmethod dual PermutableQuiver
  [^PermutableQuiver quiv]

  (PermutableQuiver.
    (morphisms quiv)
    (objects quiv)
    (target-fn quiv)
    (source-fn quiv)
    (.inv quiv)))

; Get all involution morphisms of the quiver
(defn involution-morphisms
  [quiv]

  (set
    (filter
      (fn [i]
        (= (invert-morphism quiv i) i))
      (morphisms quiv))))

(defn noninvolution-morphisms
  [quiv]

  (set
    (filter
      (fn [i]
        (not= (invert-morphism quiv i) i))
      (morphisms quiv))))

; The inversion equivalence relation is important to understanding
; the topos of permutable quivers, as it is part of the section preorder
(defn inverse-morphisms-of
  [quiv coll]

  (set
    (map
      (fn [i]
        (invert-morphism quiv i))
      coll)))

(defn inversion-equivalence-of
  [quiv coll]

  (pn
    (fn [a b]
      (= (invert-morphism quiv a) b))
    coll))

(defn inversion-equivalence
  [quiv]

  (inversion-equivalence-of quiv (morphisms quiv)))

(defn inversion-congruence-closure
  [quiver in-partition]

  (partitionize-family
    (union
      in-partition
      (set
        (map
          (fn [in-part]
            (set
              (map
                (fn [morphism]
                  (invert-morphism quiver morphism))
                in-part)))
          in-partition)))))

(defn inversion-subset-closure
  [quiver in-set]

  (union in-set (inverse-morphisms-of quiver in-set)))

(defn inversion-closed-subset?
  [quiver in-set]

  (superset?
    (list
      (inverse-morphisms-of quiver in-set)
      in-set)))

(defn inversion-congruence?
  [quiver in-partition]

  (io-relation? (inverse-function quiver) in-partition in-partition))

; Underlying families and multifamilies
(defn underlying-multifamily
  [quiv]

  (multiset
    (map
     (fn [part]
       (let [morphism (first part)]
         (set (list (source-element quiv morphism) (target-element quiv morphism)))))
     (inversion-equivalence quiv))))

(defn underlying-family
  [quiv] (set (underlying-multifamily quiv)))

; Visualize permutable quivers
(defmethod visualize PermutableQuiver
  [^PermutableQuiver quiv]

  (visualize (underlying-multifamily quiv)))

; Subobjects of permutable quivers
(defn permutable-subquiver?
  [quiv new-edges new-vertices]

  (and
    (subquiver? quiv new-edges new-vertices)
    (inversion-closed-subset? quiv new-edges)))

(defn permutable-subquiver
  [quiv new-in new-out]

  (PermutableQuiver.
    new-in
    new-out
    (source-fn quiv)
    (target-fn quiv)
    (.inv quiv)))

; Full and wide subobjects in the topos of permutable quivers
(defn wide-permutable-subquiver
  [quiver new-in]

  (permutable-subquiver
    quiver
    new-in
    (objects quiver)))

(defn full-permutable-subquiver
  [quiver new-out]

  (permutable-subquiver
    quiver
    (quiver-set-inverse-image quiver new-out)
    new-out))

; Enumeration of subobjects of a permutable quiver
(defn permutable-subquivers
  [quiv]

  (mapcat
    (fn [inversion-classes]
      (let [inversion-closed-set (apply union inversion-classes)]
        (possible-subquivers-by-in-set quiv inversion-closed-set)))
    (power-set (inversion-equivalence quiv))))

; Relations on subobjects of a permutable quivers
(defn covering-permutable-quivers
  [quiv in-set out-set]

  (union
    (set
      (map
        (fn [new-output]
          (list in-set (conj out-set new-output)))
       (difference
         (objects quiv)
         out-set)))
    (set
      (for [inversion-class (restrict-partition
                              (inversion-equivalence quiv)
                              (difference
                                (morphisms quiv)
                                in-set))
            :let [out-objects (apply
                                union
                                (map
                                  (fn [morphism]
                                    (set
                                      (list
                                        (source-element quiv morphism)
                                        (target-element quiv morphism))))
                                  inversion-class))]
            :when (superset?
                    (list
                      out-objects
                      out-set))]
        (list (union in-set inversion-class) out-set)))))

(defn permutable-subquivers-covering
  [quiv]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (covering-permutable-quivers quiv in-set out-set)))
      (permutable-subquivers quiv))))

; Get quotients of permutable quivers now
(defn permutable-quiver-congruence?
  [quiver in-partition out-partition]

  (and
    (inversion-congruence? quiver in-partition)
    (set-superpartition?
      (list
        (quiver-partition-image quiver in-partition)
        out-partition))))

(defn quotient-permutable-quiver
  [quiver in-partition out-partition]

  (->PermutableQuiver
    in-partition
    out-partition
    (fn [part]
      (projection out-partition (source-element quiver (first part))))
    (fn [part]
      (projection out-partition (target-element quiver (first part))))
    (fn [part]
      (projection in-partition (invert-morphism quiver (first part))))))

; Enumeration theory for congruences of a permutable quiver
(defn possible-permutable-quiver-input-partitions
  [quiver]

  (let [func (inverse-function quiver)]
    (for [in-partition (enumerate-set-partitions (morphisms quiver))
         :when (io-relation? func in-partition in-partition)]
     in-partition)))

(defn permutable-quiver-congruences
  [quiver]

  (set
    (mapcat
      (fn [in-partition]
        (possible-quiver-congruences-by-in-partition quiver in-partition))
      (possible-permutable-quiver-input-partitions quiver))))

; Relations on the congruences of a permutable quiver
(defn involution-equivalence-class?
  [quiver coll]

  (superset?
    (list
      (set (inverse-morphisms-of quiver coll))
      coll)))

(defn breakup-in-partition-by-inversion-order
  [quiver in-partition]

  (loop [remaining-classes (seq in-partition)
         involutions '()
         non-involutions '()]
    (if (empty? remaining-classes)
      [(set involutions) (set non-involutions)]
      (let [current-class (first remaining-classes)
            is-involution? (involution-equivalence-class? quiver current-class)]
        (recur
         (rest remaining-classes)
         (if is-involution? (cons current-class involutions) involutions)
         (if is-involution? non-involutions (cons current-class non-involutions)))))))

(defn object-preserving-permutable-quiver-covering-congruences
  [quiver in-partition out-partition]

  (let [in-class-types (breakup-in-partition-by-inversion-order quiver in-partition)
        [involution-classes non-involution-classes] in-class-types]
    (union
      (set
        (for [involution-partition (direct-set-partition-coarsifications involution-classes)
              :let [morphism-partition (union involution-partition non-involution-classes)]
              :when (set-superpartition?
                      (list
                        (quiver-partition-image quiver morphism-partition)
                        out-partition))]
          (list morphism-partition out-partition)))
      (set
        (for [non-involution-partition (direct-set-partition-coarsifications non-involution-classes)
              :let [new-in-partition (union non-involution-partition involution-classes)]
              :when (set-superpartition?
                      (list
                        (quiver-partition-image quiver new-in-partition)
                        out-partition))]
          (list
            (inversion-congruence-closure quiver new-in-partition)
            out-partition))))))

(defn permutable-quiver-covering-congruences
  [quiver in-partition out-partition]

  (union
    (set
      (map
        (fn [new-out-partition]
          (list in-partition new-out-partition))
        (direct-set-partition-coarsifications out-partition)))
    (object-preserving-permutable-quiver-covering-congruences quiver in-partition out-partition)))

(defn permutable-quiver-congruences-covering
  [quiver]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list [in-partition out-partition] [new-in-partition new-out-partition]))
          (permutable-quiver-covering-congruences quiver in-partition out-partition)))
      (permutable-quiver-congruences quiver))))

; Ontology of permutable quivers
(defmulti permutable-quiver? type)

(defmethod permutable-quiver? ::permutable-quiver
  [quiv] true)

(defmethod permutable-quiver? :default
  [quiv] false)

; Special classes of permutable quivers
(defn coreflexive-permutable-quiver?
  [quiv]

  (and
    (permutable-quiver? quiv)
    (coreflexive? (underlying-relation quiv))))

(defn irreflexive-permutable-quiver?
  [quiv]

  (and
    (permutable-quiver? quiv)
    (irreflexive? (underlying-relation quiv))))

; Special classes of thin permutable quivers
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
