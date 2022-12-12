(ns locus.set.mapping.function.indexing.func
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.numeric.nms :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.limit.product :refer :all]))

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

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this i] (nth coll i))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive IndexingFunction :locus.set.logic.structure.protocols/set-function)

; Constructor for indexing functions
(defn indexing-function
  [coll]

  (IndexingFunction. coll))

; Generalized conversion methods for indexing functions
(defmulti to-indexing-function type)

(defmethod to-indexing-function clojure.lang.Seqable
  [coll] (indexing-function (seq coll)))

(defmethod to-indexing-function IndexingFunction
  [indexing-function] indexing-function)

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
