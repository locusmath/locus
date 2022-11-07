(ns locus.elementary.preorder.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.order.core.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)
           (locus.elementary.order.core.object Poset)
           (locus.elementary.preorder.core.object Preposet)))

; Let C,D be thin categories. Then a functor f : C -> D is entirely determined by its object
; part. It follows that we can save memory by defining a special class for that only
; handles functors of thin categories. In this file, we provide that class.
(deftype MonotoneMap [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction
      (morphisms source)
      (morphisms target)
      (fn [edge]
        (map func edge))))
  (second-function [this]
    (->SetFunction
      (objects source)
      (objects target)
      func))

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      (underlying-quiver source)
      (underlying-quiver target)
      (first-function this)
      (second-function this)))

  ; Functional aspects of monotone maps
  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Monotone maps constitute functors
(derive MonotoneMap :locus.elementary.copresheaf.core.protocols/functor)

; Discrete monotone maps of preorders can be formed from set functions
(defn discrete-monotone-map
  [func]

  (->MonotoneMap
    (discrete-preorder (inputs func))
    (discrete-preorder (outputs func))
    func))

; Composition and identities of thin categories
(defmethod identity-morphism Preposet
  [obj] (MonotoneMap. obj obj identity))

(defmethod identity-morphism Poset
  [obj] (MonotoneMap. obj obj identity))

(defmethod compose* MonotoneMap
  [a b]

  (MonotoneMap.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

; Quotient related monotone maps
(defn quotient-monotone-map
  [rel partition]

  (MonotoneMap.
    (relational-preposet rel)
    (relational-preposet (cl preorder? (relation-quotient rel partition)))
    (fn [x]
      (projection partition x))))

(defn inclusion-monotone-map
  [rel coll]

  (MonotoneMap.
    (relational-preposet (subrelation rel coll))
    (relational-preposet rel)
    identity))

; We can get from structure preserving maps induced inclusion functions
; a similar technique is even possible for semigroup homomorphisms
(defn induced-inclusion
  [morphism]

  (let [source (source-object morphism)
        source-relation (underlying-relation source)
        source-vertices (underlying-set source)
        target-relation (underlying-relation (target-object morphism))]
    (inclusion-function
      source-relation
      (inflate-relation source-vertices target-relation morphism))))






