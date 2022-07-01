(ns locus.elementary.order.core.monotone-map
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.order.core.poset :refer :all]
            [locus.elementary.order.core.preposet :refer :all])
  (:import (locus.elementary.order.core.preposet Preposet)
           (locus.elementary.order.core.poset Poset)))

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
      (objects source)
      (objects target)
      func))
  (second-function [this]
    (->SetFunction
      (morphisms source)
      (morphisms target)
      (fn [edge]
        (map func edge))))

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      (underlying-quiver source)
      (underlying-quiver target)
      (->SetFunction
        (first-set source)
        (first-set target)
        (fn [[a b]]
          (list (func a) (func b))))
      (->SetFunction
        (underlying-set source)
        (underlying-set target)
        func)))

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
(derive MonotoneMap :locus.elementary.function.core.protocols/functor)

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






