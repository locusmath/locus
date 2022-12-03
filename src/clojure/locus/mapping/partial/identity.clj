(ns locus.mapping.partial.identity
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.inclusion.object :refer :all]
            [locus.base.effects.global.identity :refer :all]
            [locus.mapping.partial.function :refer :all]
            [locus.mapping.partial.bijection :refer :all]
            [locus.mapping.partial.transformation :refer :all]
            [locus.mapping.partial.permutation :refer :all])
  (:import (locus.base.effects.global.identity IdentityFunction)
           (locus.base.function.inclusion.object InclusionFunction)))

; A partial identity is an idempotent partial permutation. Partial identities commute, and since
; they are idempotent they together form a semilattice. This semilattice is essentially the
; same as the intersection semilattice of a power set.
(deftype PartialIdentity [domain coll]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  Invertible
  (inv [this] this)

  clojure.lang.IFn
  (invoke [this arg] arg)
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PartialIdentity :locus.mapping.partial.function/partial-permutation)

(defmethod defined-domain PartialIdentity
  [^PartialIdentity partial-identity]

  (.-domain partial-identity))

(defmethod compose* PartialIdentity
  [a b]

  (PartialIdentity.
    (intersection (defined-domain a) (defined-domain b))
    (source-object a)))

(defn partial-identity
  [coll parent]

  (PartialIdentity.
    coll
    parent))

(defn complement-partial-identity
  [^PartialIdentity func]

  (let [domain (.-domain func)
        coll (.-coll func)]
    (PartialIdentity.
      (difference coll domain)
      coll)))

; Generalized conversion routines for partial identities
(defmulti to-partial-identity type)

(defmethod to-partial-identity PartialIdentity
  [partial-identity] partial-identity)

(defmethod to-partial-identity :locus.base.logic.core.set/universal
  [coll]

  (PartialIdentity. coll coll))

(defmethod to-partial-identity IdentityFunction
  [^IdentityFunction func]

  (let [coll (target-object func)]
    (PartialIdentity. coll coll)))

(defmethod to-partial-identity InclusionFunction
  [^InclusionFunction func]

  (PartialIdentity. (inputs func) (outputs func)))

(defmethod to-partial-identity :locus.mapping.partial.function/partial-transformation
  [func]

  (if (not (identity-partial-function? func))
    (throw (new IllegalArgumentException))
    (partial-identity
      (defined-domain func)
      (source-object func))))

; Join and meet of partial identity functions
(defn included-partial-identity?
  [a b]

  (and
    (superset? (list (defined-domain a) (defined-domain b)))
    (superset? (list (source-object a) (source-object b)))))

(defn join-partial-identities
  [& identities]

  (partial-identity
    (apply union (map defined-domain identities))
    (apply union (map source-object identities))))

(defn meet-partial-identities
  [& identities]

  (partial-identity
    (apply intersection (map defined-domain identities))
    (apply intersection (map source-object identities))))
