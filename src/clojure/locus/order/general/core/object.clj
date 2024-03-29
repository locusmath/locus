(ns locus.order.general.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

; Preorders are the basic objects of order theory. Preorders can be seen from two different
; perspectives (1) preorders can be seen to be a special type of category, called a thin
; category, and from that they can be used to form an elementary topos of copresheaves PSh(R).
; This is handled in the theory of dependency functors, which generalize the functional
; dependencies of relations.

; Perspective (2) says that preorders are like topological spaces. By the adjoint relationship
; between order and topology, we see that every preorder corresponds directly to an Alexandrov
; topology. In this perspective, every preorder can be seen to be a means of creating a
; Grothendieck topos of sheaves Sh(T(X)) of its Alexandrov topology. So preorders have both
; an elementary and a geometric theory.

(defprotocol StructuredJoinSemilattice
  "A general protocol for categories implementing the methods of join semilattices."

  (join-fn [this]
    "The variadic join function of this join semilattice."))

(defprotocol StructuredMeetSemilattice
  "A general protocol for categories implementing the methods of meet semilattices."

  (meet-fn [this]
    "The variadic meet function of this meet semilattice."))

; A data type for describing thin categories
(deftype Preposet [coll rel]
  ConcreteObject
  (underlying-set [this] coll)

  ; Structured quivers
  StructuredDiset
  (first-set [this] rel)
  (second-set [this] coll)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver rel coll first second))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (->UnitalQuiver rel coll first second (fn [x] (list x x))))
  (identity-morphism-of [this x] (list x x))

  ; Every thin category is a function
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] rel)

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Preposet :locus.set.copresheaf.structure.core.protocols/thin-category)

; Underlying relations
(defmethod underlying-relation Preposet
  [this]

  (->SeqableRelation (.-coll this) (.-rel this) {}))

(defmethod underlying-multirelation Preposet
  [this] (underlying-relation this))

; Visualizations for preorders and partial orders
(defmethod visualize :locus.set.copresheaf.structure.core.protocols/thin-category
  [this]

  (visualize (underlying-relation this)))

(defmethod visualize :locus.set.copresheaf.structure.core.protocols/thin-skeletal-category
  [this]

  (visualize (covering-relation (underlying-relation this))))

; Ordering relations on preorders
(defn preceding-element?
  [preposet a b]

  ((underlying-relation preposet) (list a b)))

(defn comparable-elements?
  [preposet a b]

  (or
    (preceding-element? preposet a b)
    (preceding-element? preposet b a)))

(defn incomparable-elements?
  [preposet a b]

  (not (comparable-elements? preposet a b)))

(defn comparability-relation
  [preposet]

  (cl symmetric-binary-relation? (underlying-relation preposet)))

(defn underlying-covering-relation
  [structure]

  (covering-relation (underlying-relation structure)))

; Relation preorders
(defn relational-preposet
  ([coll rel]
   (Preposet. coll rel))
  ([rel]
   (relational-preposet (vertices rel) rel)))

; Conversion routines
(defmulti to-preposet type)

(defmethod to-preposet Preposet
  [this] this)

(defmethod to-preposet Quiver
  [quiv]

  (Preposet.
    (objects quiv)
    (underlying-relation quiv)))

(defmethod to-preposet :locus.set.copresheaf.structure.core.protocols/thin-category
  [category]

  (->Preposet
    (objects category)
    (underlying-relation category)))

(defmethod to-preposet :default
  [rel]

  (relational-preposet rel))

; We also need special routines for
(defmethod product :locus.set.copresheaf.structure.core.protocols/thin-category
  [& args]

  (Preposet.
    (apply cartesian-product (map underlying-set args))
    (apply product-relation (map underlying-relation args))))

(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/thin-category
  [& args]

  (Preposet.
    (apply cartesian-coproduct (map underlying-set args))
    (apply sum-relation (map underlying-relation args))))

; The dual of a preordered set
(defmethod dual Preposet
  [coll]

  (Preposet. (underlying-set coll) (transpose (underlying-relation coll))))

; Discrete preorders can be formed by sets
(defn discrete-preorder
  [coll]

  (->Preposet
    (set coll)
    (coreflexive-relation (set coll))))

; Get the last indices from a vector
(defn get-last-indices
  [coll]

  (into
    {}
    (map
      (fn [i]
        [i (.lastIndexOf coll i)])
      (set coll))))

(defn get-block-endpoint
  [coll last-indices start-index]

  (if (empty? coll)
    -1
    (let [start-element (nth coll start-index)
          len (count coll)]
      (loop [current-element start-element
             current-index start-index
             current-last-index (get last-indices start-element)]
        (if (= current-index current-last-index)
          current-index
          (let [next-index (inc current-index)]
            (if (= len next-index)
              current-index
              (let [next-element (get coll next-index)]
                (recur
                  next-element
                  next-index
                  (max current-last-index (get last-indices next-element)))))))))))

(defn get-block-points
  [coll]

  (let [last-indices (get-last-indices coll)]
    (if (empty? coll)
      []
      (let [last-index (dec (count coll))]
        (loop [block-points []
               current-index 0]
          (let [next-index (get-block-endpoint coll last-indices current-index)
                next-block-points (conj block-points [current-index (inc next-index)])]
            (if (= next-index last-index)
              next-block-points
              (recur
                next-block-points
                (inc next-index)))))))))

(defn get-block-points-decomposition
  [coll]

  (map
    (fn [[i j]]
      (subvec coll i j))
    (get-block-points coll)))

(defn get-block-sets-sequence
  [coll]

  (map
    (fn [[i j]]
      (set (subvec coll i j)))
    (get-block-points coll)))

(defn get-sequence-preorder
  [coll]

  (relational-preposet
    (set coll)
    (total-preorder (get-block-sets-sequence coll))))

; Create a weak order as preposet
(defn weak-preposet
  [coll]

  (relational-preposet (weak-order coll)))

(defn total-preposet
  [coll]

  (relational-preposet (total-preorder coll)))

(defn complete-preposet
  [coll]

  (relational-preposet (complete-relation coll)))

; Join and meet operations to be applied to preposets
(defn stronger-preorder?
  [a b]

  (and
    (= (underlying-set a) (underlying-set b))
    (superset? (list (underlying-relation a) (underlying-relation b)))))

(defn join-preposets
  [& preposets]

  (->Preposet
    (apply union (map objects preposets))
    (cl transitive? (apply union (map underlying-relation preposets)))))

(defn meet-preposets
  [& preposets]

  (->Preposet
    (apply intersection (map objects preposets))
    (apply intersection (map underlying-relation preposets))))

; Subobjects of preorders
(defn subpreposet
  [preposet new-objects new-morphisms]

  (->Preposet
    new-objects
    new-morphisms))

(defn wide-subpreposet
  [preposet new-morphisms]

  (subpreposet preposet (objects preposet) new-morphisms))

(defn full-subpreposet
  [preposet new-objects]

  (->Preposet
    new-objects
    (subrelation (underlying-relation preposet) new-objects)))



