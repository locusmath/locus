(ns locus.elementary.category.relation.partial-bijection
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.base.function.inclusion.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.elementary.category.relation.partial-function :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.bijection.core.object Bijection)
           (clojure.lang PersistentArrayMap)))

; The category of sets and partial bijections is a subcategory of the category
; of partial functions, which itself can be itself be considered to be a subcategory
; of the topos Sets defined by adjoining a fixed point element representing
; the empty set, so that elements can map to the empty set to indicate they
; are not defined there. Partial bijections don't need to be surjective, so
; any injective function can be represented as a partial bijection.
(deftype PartialBijection [domain codomain source target forward backward]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  Invertible
  (inv [this]
    (PartialBijection.
      codomain
      domain
      target
      source
      backward
      forward))

  StructuredDiset
  (first-set [this] source)
  (second-set [this] target)

  clojure.lang.IFn
  (invoke [this arg]
    (forward arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive PartialBijection :locus.elementary.category.relation.partial-function/partial-bijection)

; Defined domains and codomains
(defmethod defined-domain PartialBijection
  [^PartialBijection func]

  (.domain func))

(defmethod partial-function-image PartialBijection
  [^PartialBijection func]

  (.codomain func))

; Composition and identities in the category of partial bijections
(defn partial-identity-bijection
  [coll]

  (PartialBijection.
    coll
    coll
    coll
    coll
    (fn [x] x)
    (fn [x] x)))

(defmethod compose* :locus.elementary.category.relation.partial-function/partial-bijection
  [a b]

  (let [new-domain (set
                     (filter
                       (fn [i]
                         (let [next-val (b i)]
                           (boolean
                             ((defined-domain a) next-val))))
                       (defined-domain b)))
        new-codomain (set
                       (map
                         (fn [i]
                           (a (b i)))
                         new-domain))]
    (PartialBijection.
      new-domain
      new-codomain
      (source-object b)
      (target-object a)
      (comp (.forward a) (.forward b))
      (comp (.backward a) (.backward b)))))

; Empty partial bijections
(defn empty-partial-bijection
  [a b]

  (PartialBijection.
    #{}
    #{}
    a
    b
    (fn [x] x)
    (fn [x] x)))

; Convert objects to partial bijections
(defmulti to-partial-bijection type)

(defmethod to-partial-bijection Bijection
  [^Bijection func]

  (PartialBijection.
    (inputs func)
    (outputs func)
    (inputs func)
    (outputs func)
    (.-forward func)
    (.-backward func)))

(defmethod to-partial-bijection :locus.base.logic.structure.protocols/inclusion-function
  [func]

  (let [a (inputs func)
        b (outputs func)]
    (PartialBijection.
      a
      a
      a
      b
      (fn [x] x)
      (fn [x] x))))

; Underlying partial functions
(defmethod to-partial-function PartialBijection
  [^PartialBijection func]

  (->PartialFunction
    (defined-domain func)
    (source-object func)
    (target-object func)
    (.forward func)))

; Total components of partial bijections
(defmethod total-component PartialBijection
  [^PartialBijection func]

  (Bijection.
    (defined-domain func)
    (partial-function-image func)
    (.-forward func)
    (.-backward func)))