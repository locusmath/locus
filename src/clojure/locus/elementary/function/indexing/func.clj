(ns locus.elementary.function.indexing.func
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.nms :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]))

; An indexing function is essentially just a presentation of an ordinary
; sequence like (a,b,c) as a function from a subset of the natural numbers
; to the value at the index in the list. This allows for lists and sequences
; to be treated like objects in the topos of functions, for example, when
; constructing subobject and congruence lattices.

(deftype IndexingFunction [coll]
  ConcreteMorphism
  (inputs [this] (->Upto (count coll)))
  (outputs [this] (set coll))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  StructuredDiset
  (first-set [this] (inputs this))
  (second-set [this] (outputs this))

  clojure.lang.IFn
  (invoke [this i] (nth coll i))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive IndexingFunction :locus.elementary.function.core.protocols/set-function)

; Constructor for indexing functions
(defn indexing-function
  [coll]

  (IndexingFunction. coll))

; Ontology of indexing functions
(defmulti indexing-function? type)

(defmethod indexing-function? IndexingFunction
  [func] true)

(defmethod indexing-function? :default
  [func]

  (and
    (set-function? func)
    (natural-range? (inputs func))))

(defn injective-indexing-function?
  [func]

  (and
    (injective? func)
    (indexing-function? func)))

(defn constant-indexing-function?
  [func]

  (and
    (indexing-function? func)
    (constant-function? func)))
