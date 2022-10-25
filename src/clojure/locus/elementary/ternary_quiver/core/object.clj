(ns locus.elementary.ternary-quiver.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]))

; Objects in the topos Sets^{T_{2,3}} of copresheaves over an index category consisting of two
; objects and with three morphisms between them. While binary quivers describe the topos theory
; of directed and undirected graphs, ternary quivers are the foundation for the topos theory
; of algebra. We say that a binary operation f: X^2 -> X is actually a pair of sets
; X^2 and X with three operations between them: the first accessor, the second accessor,
; and the composition function. So that makes binary operations ought to be special cases
; of ternary quivers.

; A ternary quiver should implement the diset and ternary quiver protocols
(defprotocol StructuredTernaryQuiver
  "A structured ternary quiver is any object of a category equipped with a forgetful functor
  F: C -> Sets^{T_{2,3}} to the topos of ternary quivers. This protocol defines methods for handling
  objects with reference to their forgetful functors to the topos of ternary quivers. In particular,
  every morphism of a ternary quiver is associated with a triple of component values by evaluating
  all the component functions of the ternary quiver at the morphism."

  (first-component-fn [this]
    "The first component of a morphism of a ternary quiver.")
  (second-component-fn [this]
    "The second component of a morphism of a ternary quiver.")
  (third-component-fn [this]
    "The third component of a morphism of a ternary quiver."))

; Ternary quiver objects
(deftype TernaryQuiver [edges vertices first second third]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(first-set this) (second-set this)]))

  StructuredTernaryQuiver
  (first-component-fn [this] first)
  (second-component-fn [this] second)
  (third-component-fn [this] third))

(derive TernaryQuiver :locus.elementary.copresheaf.core.protocols/ternary-quiver)

; Component functions of a ternary quiver
(defn first-component
  [^TernaryQuiver q, e]

  ((first-component-fn q) e))

(defn second-component
  [^TernaryQuiver q, e]

  ((second-component-fn q) e))

(defn third-component
  [^TernaryQuiver q, e]

  ((third-component-fn q) e))

(defn first-component-function
  [quiver]

  (->SetFunction
    (morphisms quiver)
    (objects quiver)
    (first-component-fn quiver)))

(defn second-component-function
  [quiver]

  (->SetFunction
    (morphisms quiver)
    (objects quiver)
    (second-component-fn quiver)))

(defn third-component-function
  [quiver]

  (->SetFunction
    (morphisms quiver)
    (objects quiver)
    (third-component-fn quiver)))

; Components of ternary quivers
(defmethod get-set :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiver x]

  (case x
    0 (morphisms quiver)
    1 (objects quiver)))

(defmethod get-function :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiver x]

  (case x
    0 (identity-function (morphisms quiver))
    1 (identity-function (objects quiver))
    2 (first-component-function quiver)
    3 (second-component-function quiver)
    4 (third-component-function quiver)))

; Underlying relations and multirelations for ternary quivers
(defn transition-triple
  [^TernaryQuiver q, e]

  (list
    (first-component q e)
    (second-component q e)
    (third-component q e)))

(defmethod underlying-multirelation TernaryQuiver
  [^TernaryQuiver q]

  (multiset
    (map
      (fn [e]
        (transition-triple q e))
      (morphisms q))))

(defmethod underlying-relation TernaryQuiver
  [^TernaryQuiver q]

  (set
    (underlying-multirelation q)))

; A ternary quiver has three different types of binary quivers associated to it
(defn front-quiver
  [quiver]

  (->Quiver
    (morphisms quiver)
    (objects quiver)
    (first-component-fn quiver)
    (second-component-fn quiver)))

(defn back-quiver
  [quiver]

  (->Quiver
    (morphisms quiver)
    (objects quiver)
    (second-component-fn quiver)
    (third-component-fn quiver)))

(defn outer-quiver
  [quiver]

  (->Quiver
    (morphisms quiver)
    (objects quiver)
    (first-component-fn quiver)
    (third-component-fn quiver)))

; Create a ternary quiver from a ternary relation
(defn relational-ternary-quiver
  ([rel]
   (relational-ternary-quiver (vertices rel) rel))

  ([vertex-set rel]
   (->TernaryQuiver
     rel
     vertex-set
     first
     second
     #(nth % 2))))

; A ternary quiver with no morphisms
(defn empty-ternary-quiver
  [coll]

  (->TernaryQuiver
    #{}
    coll
    first
    second
    #(nth % 2)))

; Ternary quivers with only a single object
(defn singular-ternary-quiver
  [coll obj]

  (->TernaryQuiver
    coll
    #{obj}
    (constantly obj)
    (constantly obj)
    (constantly obj)))

; Coreflexive ternary quivers
(defn coreflexive-ternary-quiver
  [func]

  (->TernaryQuiver
    (inputs func)
    (outputs func)
    func
    func
    func))

; Generalized conversion methods for ternary quivers
(defmulti to-ternary-quiver type)

(defmethod to-ternary-quiver TernaryQuiver
  [^TernaryQuiver quiver] quiver)

(defmethod to-ternary-quiver :locus.base.logic.core.set/universal
  [coll] (relational-ternary-quiver coll))

(defmethod to-ternary-quiver :locus.base.logic.structure.protocols/set-function
  [func]

  (->TernaryQuiver
    (inputs func)
    (outputs func)
    first
    second
    func))

; Generalized hom classes in the topos of ternary quivers
(defn ternary-quiver-hom-class
  [quiver a b c]

  (set
    (filter
      (fn [morphism]
        (and
          (= (first-component quiver morphism) a)
          (= (second-component quiver morphism) b)
          (= (third-component quiver morphism) c)))
      (morphisms quiver))))

(defn ternary-quiver-hom-class-cardinality
  [quiver a b c]

  (count (ternary-quiver-hom-class quiver a b c)))

; Products and coproducts in the topos of ternary quivers
(defn ternary-quiver-product
  [& quivers]

  (TernaryQuiver.
    (apply product (map morphisms quivers))
    (apply product (map objects quivers))
    (fn [coll]
      (map-indexed
        (fn [i v]
          (first-component (nth quivers i) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          (second-component (nth quivers i) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          (third-component (nth quivers i) v))
        coll))))

(defn ternary-quiver-coproduct
  [& quivers]

  (TernaryQuiver.
    (apply coproduct (map morphisms quivers))
    (apply coproduct (map objects quivers))
    (fn [[i v]]
      (list i (first-component (nth quivers i) v)))
    (fn [[i v]]
      (list i (second-component (nth quivers i) v)))
    (fn [[i v]]
      (list i (third-component (nth quivers i) v)))))

; Images and inverse images in the topos Sets^{T_{2,3}} of ternary quivers
; Images and inverse images are described naturally in terms of the topos Sets^(->) which leads to
; the familiar conceptions of images and inverse images of sets in classical set theory. These
; basic notions can be generalized to a number of other topoi, including the topos of ternary
; quivers which helps us to reason about subobjects and congruences in Sets^{T_{2,3}}.
(defn ternary-quiver-set-image
  [quiver coll]

  (apply
    union
    (map
      (fn [i]
        (set (transition-triple quiver i)))
      coll)))

(defn ternary-quiver-set-inverse-image
  [quiver coll]

  (set
    (filter
      (fn [morphism]
        (and
          (contains? coll (first-component quiver morphism))
          (contains? coll (second-component quiver morphism))
          (contains? coll (third-component quiver morphism))))
      morphisms)))

(defn ternary-quiver-partition-image
  [quiver partition]

  (join-set-partitions
    (partition-image (first-component-function quiver) partition)
    (partition-image (second-component-function quiver) partition)
    (partition-image (third-component-function quiver) partition)))

(defn ternary-quiver-partition-inverse-image
  [quiver partition]

  (meet-set-partitions
    (partition-inverse-image (first-component-function quiver) partition)
    (partition-inverse-image (second-component-function quiver) partition)
    (partition-inverse-image (third-component-function quiver) partition)))

; Subobjects in the topos of ternary quivers
(defn ternary-subquiver
  [quiver new-edges new-vertices]

  (->TernaryQuiver
    new-edges
    new-vertices
    (first-component-fn quiver)
    (second-component-fn quiver)
    (third-component-fn quiver)))

(defn full-ternary-subquiver
  [quiver new-vertices]

  (->TernaryQuiver
    (ternary-quiver-set-inverse-image quiver new-vertices)
    new-vertices
    (first-component-fn quiver)
    (second-component-fn quiver)
    (third-component-fn quiver)))

(defn wide-ternary-subquiver
  [quiver new-edges]

  (ternary-subquiver quiver new-edges (objects quiver)))

; Checking for ternary subquivers
(defn ternary-subquiver?
  [quiver in-set out-set]

  (superset?
    (list
      (ternary-quiver-set-image quiver in-set)
      out-set)))

(defn ternary-subquiver-closure
  [quiver new-in new-out]

  (list
    new-in
    (union new-out (ternary-quiver-set-image quiver new-in))))

; Enumeration theory for all subobjects of a ternary quiver
(defn ternary-subquivers
  [quiver]

  (set
    (mapcat
      (fn [in-set]
        (let [minimal-out-set (ternary-quiver-set-image quiver in-set)
              possible-out-additions (difference (objects quiver) minimal-out-set)]
          (map
            (fn [out-additions]
              (list in-set (union minimal-out-set out-additions)))
            (power-set possible-out-additions))))
      (power-set (morphisms quiver)))))

; Covering relations for ternary quivers
(defn covering-ternary-subquivers
  [quiver in-set out-set]

  (set
    (concat
      (for [i (difference (morphisms quiver) in-set)
            :when (ternary-subquiver? quiver #{i} out-set)]
        (list (conj in-set i) out-set))
      (for [i (difference (objects quiver) out-set)]
        (list in-set (conj out-set i))))))

(defn ternary-subquivers-covering
  [quiv]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (covering-ternary-subquivers quiv in-set out-set)))
      (ternary-subquivers quiv))))

; Quotients in the topos of ternary quivers
(defn ternary-quotient-quiver
  [quiver edge-partition vertex-partition]

  (->TernaryQuiver
    edge-partition
    vertex-partition
    (fn [part]
      (projection edge-partition (first-component quiver (first part))))
    (fn [part]
      (projection edge-partition (second-component quiver (first part))))
    (fn [part]
      (projection edge-partition (third-component quiver (first part))))))

; Check for congruences in the topos of ternary quivers
(defn ternary-quiver-congruence?
  [quiver in-partition out-partition]

  (set-superpartition?
    (list
      (ternary-quiver-partition-image quiver in-partition)
      out-partition)))

(defn ternary-quiver-congruence-closure
  [quiver in-partition out-partition]

  (list
    in-partition
    (join-set-partitions
      out-partition
      (ternary-quiver-partition-image quiver in-partition))))

; Congruences of ternary quivers
(defn ternary-quiver-congruences
  [quiver]

  (set
    (mapcat
      (fn [in-partition]
        (let [current-image-partition (ternary-quiver-partition-image quiver in-partition)]
          (map
            (fn [out-partition]
              (list in-partition out-partition))
            (set-partition-coarsifications current-image-partition))))
      (enumerate-set-partitions (morphisms quiver)))))

; Covering relation on congruences of ternary quivers
(defn ternary-quiver-covering-congruences
  [quiver in-set out-set]

  (concat
    (set
      (for [i (direct-set-partition-coarsifications in-set)
            :when (set-superpartition?
                    (list (ternary-quiver-partition-image quiver i) out-set))]
        (list i out-set)))
    (set
      (for [i (direct-set-partition-coarsifications out-set)]
        (list in-set i)))))

(defn ternary-quiver-congruences-covering
  [quiver]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list [in-partition out-partition] [new-in-partition new-out-partition]))
          (ternary-quiver-covering-congruences quiver in-partition out-partition)))
      (ternary-quiver-congruences quiver))))

; Ontology of ternary quivers
(defmulti ternary-quiver? type)

(defmethod ternary-quiver? :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiv] true)

(defmethod ternary-quiver? :default
  [obj] false)

(defmulti thin-ternary-quiver? type)

(defmethod thin-ternary-quiver? :locus.elementary.copresheaf.core.protocols/thin-ternary-quiver
  [quiv] true)

(defmethod thin-ternary-quiver? :default
  [quiv]

  (and
    (ternary-quiver? quiv)
    (universal? (underlying-multirelation quiv))))

(defmulti at-quiver? type)

(defmethod at-quiver? :locus.elementary.copresheaf.core.protocols/at-quiver
  [quiv] true)

(defmethod at-quiver? :default
  [quiv]

  (and
    (thin-ternary-quiver? quiv)
    (let [rel (underlying-relation quiv)]
      (satisfies-functional-dependency? rel #{0 1} #{2}))))
