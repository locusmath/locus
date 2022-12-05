(ns locus.sub.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.inclusion.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; Objects in the category of sets with unary relations on them. Given a set S a unary relation R
; on S is equivalent to a subset of S.
(deftype SetSubalgebra [coll parent]
  ConcreteObject
  (underlying-set [this] parent))

(derive ::set-subalebra :locus.base.logic.structure.protocols/structured-set)
(derive SetSubalgebra ::set-subalebra)

; Included and excluded elements of subalgebras of sets
(defmulti included-elements type)

(defmethod included-elements SetSubalgebra
  [^SetSubalgebra coll]

  (.-coll coll))

(defn excluded-elements
  [coll]

  (difference (underlying-set coll) (included-elements coll)))

; A constructor for set subalgebras
(defn set-subalgebra
  [a b]

  (SetSubalgebra. a b))

(defn full-set-subalgebra
  [coll]

  (SetSubalgebra. coll coll))

(defn empty-set-subalgebra
  [coll]

  (SetSubalgebra. #{} coll))

; Subalgebras form a category that admits complementation on objects
(defn complement-set-subalgebra
  [coll]

  (->SetSubalgebra
    (difference (underlying-set coll) (included-elements coll))
    (underlying-set coll)))

; Conversion routines to turn subsets into inclusion functions
(defmethod to-function SetSubalgebra
  [set-subalgebra]

  (->InclusionFunction (included-elements set-subalgebra) (underlying-set set-subalgebra)))

; Conversion routines for set subalgebras
(defmulti to-set-subalgebra type)

(defmethod to-set-subalgebra SetSubalgebra
  [^SetSubalgebra subalgebra] subalgebra)

(defmethod to-set-subalgebra :locus.base.logic.structure.protocols/inclusion-function
  [func]

  (SetSubalgebra. (inputs func) (outputs func)))

(defmethod to-set-subalgebra :locus.base.logic.core.set/universal
  [coll]

  (full-set-subalgebra coll))

; Product and coproducts of set subalgebras
(defmethod product ::set-subalebra
  [& sets]

  (->SetSubalgebra
    (apply product (map included-elements sets))
    (apply product (map underlying-set sets))))

(defmethod coproduct ::set-subalebra
  [& sets]

  (->SetSubalgebra
    (apply coproduct (map included-elements sets))
    (apply coproduct (map underlying-set sets))))

; Ontology of set subalgebras
(defmulti set-subalgebra? type)

(defmethod set-subalgebra? ::set-subalebra
  [subalgebra] true)

(defmethod set-subalgebra? :default
  [obj] false)

(defn pointed-set?
  [obj]

  (and
    (set-subalgebra? obj)
    (= (count (included-elements obj)) 1)))