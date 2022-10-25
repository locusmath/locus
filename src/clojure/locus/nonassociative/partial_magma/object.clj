(ns locus.nonassociative.partial-magma.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (clojure.lang IPersistentMap)))

; A partial magma is a copresheaf in the topos of ternary quivers. Its morphism set is the set
; of ordered pairs R, and its objects are the underlying set of the partial magma as a
; ternary quiver. Its three functions are the first projection function, the second projection
; function, and the algebraic operation of the partial magma.
(deftype PartialMagma [coll rel op]
  ConcreteObject
  (underlying-set [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver coll 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] rel)
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PartialMagma :locus.elementary.copresheaf.core.protocols/partial-magma)

; Path quivers of partial magmas
(defmethod paths PartialMagma
  [^PartialMagma magma]

  (.-rel magma))

(defmethod underlying-path-quiver PartialMagma
  [^PartialMagma magma]

  (singular-relational-path-quiver (morphisms magma) (paths magma) #{0}))

; Create a domain quiver from a partial magma
(defn domain-quiver
  [^PartialMagma magma]

  (relational-quiver (morphisms magma) (paths magma)))

; Get the composition operation of a category or other magmoid as a partial operation
(defn composition-operation
  [magmoid]

  (->PartialMagma
    (morphisms magmoid)
    (paths magmoid)
    (fn [[a b]]
      (magmoid (list a b)))))

(defn composition-exists?
  [magmoid a b]

  ((inputs magmoid) (list a b)))

; Check for the existence of iterations in a partial magmoa
(defn iteration-exists?
  [magmoid a]

  (composition-exists? magmoid a a))

(defn iteration-existent-elements
  [magmoid]

  (set
    (filter
      (fn [morphism]
        (iteration-exists? magmoid morphism))
      (morphisms magmoid))))

; Create a partial operation describing the composition of ordered pairs
(defn transition-partial-magma
  [rel]

  (->PartialMagma
    rel
    (composability-relation (to-quiver rel))
    compose-ordered-pairs))

; Conversion routines for partial magmas
(defmulti to-partial-magma type)

(defmethod to-partial-magma PartialMagma
  [magma] magma)

(defmethod to-partial-magma SetFunction
  [func]

  (PartialMagma.
    (union (vertices (inputs func)) (outputs func))
    (inputs func)
    (.func func)))

(defmethod to-partial-magma IPersistentMap
  [coll]

  (to-partial-magma (mapfn coll)))

; Products and coproducts in the category of partial magmas
(defmethod product PartialMagma
  [& magmas]

  (PartialMagma.
    (apply product (map morphisms magmas))
    (apply product-relation (map paths magmas))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i magmoid]
          (magmoid (list (nth morphisms1 i) (nth morphisms2 i))))
        magmas))))

; Coproducts of partial magmas as partial algebras instead of single object partial magmoids
(defn sum-partial-magma
  [& magmas]

  (PartialMagma.
    (apply coproduct (map morphisms magmas))
    (apply sum-relation (map paths magmas))
    (fn [[[i a] [j b]]]
      (list i ((nth magmas i) (list a b))))))

; Duals of partial magmas
(defmethod dual PartialMagma
  [magma]

  (PartialMagma.
    (morphisms magma)
    (transpose (paths magma))
    (comp magma reverse)))

; Subobjects of partial magmas
(defn partial-submagma
  [magma new-domain new-coll]

  (->PartialMagma
    new-coll
    new-domain
    (.-op magma)))

(defn restrict-partial-magma
  [magma new-domain]

  (partial-submagma magma new-domain (morphisms magma)))

(defn domain-full-partial-submagma
  [magma new-coll]

  (let [full-domain (set
                      (filter
                        (fn [[a b]]
                          (and
                            (boolean (new-coll a))
                            (boolean (new-coll b))))
                        (inputs magma)))]
    (partial-submagma magma full-domain new-coll)))

; Test for partial submagmas
(defn partial-submagma?
  [magma new-domain coll]

  (every?
    (fn [[a b]]
      (contains? coll (magma (list a b))))
    new-domain))

(defn domain-full-partial-submagma?
  [magma new-morphisms]

  (compositionally-closed-set? magma new-morphisms))

(defn domain-full-partial-submagmas
  [magma]

  (set
    (filter
      (fn [coll]
        (domain-full-partial-submagma? magma coll))
      (power-set (morphisms magma)))))

; Congruences in the topos of ternary quivers for partial magmas
(defn partial-magma-congruence?
  [magma partition]

  (compositional-congruence? magma partition))

(defn partial-magma-congruences
  [magma]

  (filter
    (fn [morphism-partition]
      (partial-magma-congruence? magma morphism-partition))
    (enumerate-set-partitions (set (morphisms magma)))))

(defn quotient-partial-magma
  [magma partition]

  (->PartialMagma
    partition
    (extend-partition-to-relation partition (paths magma))
    (fn [[a b]]
      (projection
        partition
        (magma (list (first a) (first b)))))))

; Ontology of partial magmas
(defmulti partial-magma? type)

(defmethod partial-magma? :locus.elementary.copresheaf.core.protocols/partial-magma
  [obj] true)

(defmethod partial-magma? :locus.elementary.copresheaf.core.protocols/partial-magmoid
  [obj]

  (= (count (objects obj)) 1))

(defmethod partial-magma? :default
  [obj] false)

; A domain coreflexive partial magma is like a function
(defn domain-coreflexive-partial-magma?
  [obj]

  (and
    (partial-magma? obj)
    (coreflexive? (inputs obj))))

(defn domain-irreflexive-partial-magma?
  [obj]

  (and
    (partial-magma? obj)
    (irreflexive? (inputs obj))))

; Idempotentence in the context of partial magmas
(defn idempotent-partial-magma?
  [magma]

  (and
    (partial-magma? magma)
    (every?
     (fn [arrow]
       (and
         (composition-exists? magma arrow arrow)
         (= arrow (magma (list arrow arrow)))))
     (morphisms magma))))

(defn partially-idempotent-partial-magma?
  [magma]

  (and
    (partial-magma? magma)
    (every?
     (fn [arrow]
       (or
         (not (composition-exists? magma arrow arrow))
         (= arrow (magma (list arrow arrow)))))
     (morphisms magma))))

(defn commutative-partial-magma?
  [magma]

  (and
    (partial-magma? magma)
    (every?
      (fn [[a b]]
        (or
          (and
            (not (composition-exists? magma a b))
            (not (composition-exists? magma b a)))
          (and
            (composition-exists? magma a b)
            (composition-exists? magma b a)
            (= (magma (list a b))
               (magma (list b a))))))
      (cartesian-power (morphisms magma) 2))))


