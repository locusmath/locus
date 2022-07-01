(ns locus.elementary.relational.function.partial-set-function
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)
           (locus.elementary.bijection.core.object Bijection)
           (clojure.lang PersistentArrayMap)))

; Partial set functions form a special category: the category of sets and
; functions between them. This is a subcategory of Rel, the category of sets
; and relations and it is a supercategory of the topos Sets of sets and functions.
; It is important, for example in semigroup theory, that we can construct this
; category to define for example semigroups of partial transformations and
; partial permutations.
(deftype PartialSetFunction [domain source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDiset
  (first-set [this] source)
  (second-set [this] target)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Ontology of derivations
(derive ::partial-transformation ::partial-set-function)
(derive ::partial-bijection ::partial-set-function)
(derive ::partial-permutation ::partial-transformation)
(derive ::partial-permutation ::partial-bijection)
(derive ::atomic-chart ::partial-permutation)
(derive PartialSetFunction ::partial-set-function)

; The defined domain is where the value of the partial set function is not zero
(defmulti defined-domain type)

(defmethod defined-domain PartialSetFunction
  [^PartialSetFunction x]

  (.-domain x))

(defmethod defined-domain :locus.elementary.function.core.protocols/set-function
  [func]

  (inputs func))

; Category of partial set functions
(defn partial-identity-function
  [coll]

  (PartialSetFunction. coll coll coll (fn [i] i)))

(defmethod compose* ::partial-set-function
  [a b]

  (let [new-defined-domain (set
                             (filter
                               (fn [i]
                                 (let [next-val (b i)]
                                   (boolean
                                     ((defined-domain a) next-val))))
                               (defined-domain b)))]
    (PartialSetFunction.
      new-defined-domain
      (source-object b)
      (target-object a)
      (fn [x]
        (a (b x))))))

; Underlying relations for all partial set functions
(defmethod underlying-relation ::partial-set-function
  [func]

  (set
    (map
      (fn [i]
        (list i (func i)))
      (defined-domain func))))

(defmethod visualize ::partial-set-function
  [func]

  (visualize (underlying-relation func)))

; Dual concepts of missing inputs and outputs exist for partial set functions
(defn missing-inputs
  [func]

  (difference (source-object func) (defined-domain func)))

(defn missing-outputs
  [func]

  (difference
    (target-object func)
    (set
      (map
        (fn [i]
          (func i))
        (defined-domain func)))))

; Images generalised for partial functions
(defn partial-function-image
  [func]

  (set
    (map
      (fn [i]
        (func i))
      (defined-domain func))))

; Empty partial set functions have an empty defined domain
(defn empty-partial-set-function
  [source target]

  (PartialSetFunction.
    #{}
    source
    target
    (fn [x] x)))

; Conversion routines
(defmulti to-partial-set-function type)

(defmethod to-partial-set-function PartialSetFunction
  [func] func)

(defmethod to-partial-set-function SetFunction
  [func]

  (PartialSetFunction.
    (inputs func)
    (inputs func)
    (outputs func)
    (fn [x]
      (func x))))

(defmethod to-partial-set-function Bijection
  [func]

  (to-partial-set-function (underlying-function func)))

; Partial set function -> total set function
(defn total-component
  [func]

  (SetFunction.
    (defined-domain func)
    (outputs func)
    (fn [i]
      (func i))))

; Ontology of partial set functions
(defn partial-set-function?
  [x]

  (isa? (type x) ::partial-set-function))

(defmulti partial-transformation? type)

(defmethod partial-transformation? ::partial-transformation
  [x] true)

(defmethod partial-transformation? :default
  [x]

  (and
    (partial-set-function? x)
    (= (source-object x) (target-object x))))

(defmulti partial-bijection? type)

(defmethod partial-bijection? ::partial-bijection
  [x] true)

(defmethod partial-bijection? ::partial-set-function
  [x]

  (and
    (partial-set-function? x)
    (let [domain (seq (defined-domain x))]
      (loop [remaining-elements domain
             mapped-outputs '()]
        (or
          (empty? remaining-elements)
          (let [next-element (first remaining-elements)
                next-output (x next-element)
                new-element? (every?
                               (fn [mapped-output]
                                 (not= mapped-output next-output))
                               mapped-outputs)]
            (and
              new-element?
              (recur
                (rest remaining-elements)
                (cons next-output mapped-outputs)))))))))

(defmethod partial-bijection? :default
  [x] false)

(defmulti partial-permutation? type)

(defmethod partial-permutation? ::partial-permutation
  [x] true)

(defmethod partial-permutation? :default
  [x]

  (and
    (partial-bijection? x)
    (= (source-object x) (target-object x))))

(defmulti atomic-chart? type)

(defmethod atomic-chart? ::atomic-chart
  [x] true)

(defmethod atomic-chart? ::partial-transformation
  [x]

  (= (count (defined-domain x)) 1))

(defmethod atomic-chart? :default
  [x]

  (and
    (partial-set-function? x)
    (= (source-object x) (target-object x))
    (= (count (defined-domain x)) 1)))

(defn surjective-partial-function?
  [x]

  (and
    (partial-set-function? x)
    (empty? (missing-outputs x))))

(defn surjective-partial-bijection?
  [x]

  (and
    (partial-bijection? x)
    (empty? (missing-outputs x))))

(defn empty-partial-function?
  [x]

  (and
    (partial-set-function? x)
    (= (count (defined-domain x)) 0)))

(defn identity-partial-function?
  [x]

  (and
    (partial-set-function? x)
    (every?
      (fn [i]
        (= (x i) i))
      (defined-domain x))))

(defn identity-partial-permutation?
  [x]

  (and
    (identity-partial-function? x)
    (= (source-object x) (target-object x))))

