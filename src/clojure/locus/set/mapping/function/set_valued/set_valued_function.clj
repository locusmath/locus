(ns locus.set.mapping.function.set-valued.set-valued-function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]))

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

(derive SetValuedFunction :locus.set.logic.structure.protocols/set-function)

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

(defmethod set-valued-function? :default
  [func]

  (every?
    (fn [i]
      (universal? (func i)))
    (inputs func)))

; Injective and constant types of set valued functions
(def injective-set-valued-function?
  (intersection
    injective?
    set-valued-function?))

(def constant-set-valued-function?
  (intersection
    constant-function?
    set-valued-function?))

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
    (every? (comp empty? func) (inputs func))))

(defn rank-one-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp unique-universal? func) (inputs func))))

(defn rank-two-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp max-size-two-universal? func) (inputs func))))

(defn rank-three-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp max-size-three-universal? func) (inputs func))))

(defn rank-four-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp max-size-four-universal? func) (inputs func))))

; Special classes of set valued functions by their cardinalities
(defn uniform-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (equal-seq?
      (map
        (fn [i]
          (count (func i)))
        (inputs func)))))

(defn unary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp singular-universal? func) (inputs func))))

(defn binary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp size-two-universal? func) (inputs func))))

(defn ternary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp size-three-universal? func) (inputs func))))

(defn quaternary-set-valued-function?
  [func]

  (and
    (set-valued-function? func)
    (every? (comp size-four-universal? func) (inputs func))))