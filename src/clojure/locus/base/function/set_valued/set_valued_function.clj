(ns locus.base.function.set-valued.set-valued-function
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]))

; A set valued function is a function from one set to the power set of another set
(deftype SetValuedFunction [source target func]
  ConcreteMorphism
  (inputs [this] source)
  (outputs [this] (->PowerSet target))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive SetValuedFunction :locus.base.logic.structure.protocols/set-function)

; Methods for creating set valued functions
(defn set-valued-function
  [source target func]

  (SetValuedFunction.
    source
    target
    func))

; Get a flags relation from a set valued function
(defn function-flags
  [func]

  (apply
    union
    (set
      (map
        (fn [x]
          (set
            (map
              (fn [y]
                (list x y))
              (func x))))
        (inputs func)))))

(defn function-lines
  [func]

  (dimembers (outputs func)))

(defn embedded-function-flags
  [func]

  (let [in (inputs func)
        out (function-lines func)
        rel (seqable-filter
              (->CartesianPower (union in out) 2)
              (fn [[a b]]
                ((func a) b)))]
    (embedded-relation rel in out)))

; Create a set valued function
(defn dual-incidence-function
  [func]

  (let [in (inputs func)
        out (function-lines func)]
    (set-valued-function
      out
      in
      (fn [line]
        (set
          (filter
            (fn [point]
              (contains? (func point) line))
            in))))))

; Ontology of set valued functions
(defmulti set-valued-function? type)

(defmethod set-valued-function? SetValuedFunction
  [func] true)

; Injective and constant types of set valued functions
(defn injective-set-valued-function?
  [func]

  (and
    (injective? func)
    (set-valued-function? func)))

(defn constant-set-valued-function?
  [func]

  (and
    (constant-function? func)
    (set-valued-function? func)))

; Reflexivity conditions
(defn reflexive-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [i]
        (boolean ((func i) i)))
      (inputs func))))

(defn irreflexive-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [i]
        (not (boolean ((func i) i))))
      (inputs func))))

; Special types of set valued functions
(defn empty-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [i]
        (empty? (func i)))
      (inputs func))))

(defn unary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [x]
        (singular-universal? (func x)))
      (inputs func))))

(defn binary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [x]
        (size-two-universal? (func x)))
      (inputs func))))

(defn ternary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [x]
        (size-three-universal? (func x)))
      (inputs func))))

(defn quaternary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every?
      (fn [x]
        (size-four-universal? (func x)))
      (inputs func))))