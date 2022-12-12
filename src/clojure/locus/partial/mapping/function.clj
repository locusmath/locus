(ns locus.partial.mapping.function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.function.inclusion.object :refer :all]
            [locus.set.mapping.function.image.image-function :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (clojure.lang PersistentArrayMap IPersistentMap)
           (locus.set.mapping.function.inclusion.object InclusionFunction)))

; Partial functions form a concrete category PF of sets and partial functions
; between them. The category of partial functions can be considered to be
; the subcategory of the topos Sets that consists of sets and functions
; with a fixed point element adjoined represented the empty set. This way,
; elements can map to the empty set to indicate that they are not defined there.
; The subcategory of image functions is a yet larger category.

; A second categorical perspective on partial functions arises from consideration
; of the topos of spans. In this context, a partial function can be defined
; by a pair of functions with a common origin set, one of which is an
; inclusion and the other of which is the underlying total function. This second
; perspective can be used to implement products and coproducts of partial functions.
(deftype PartialFunction [domain source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Ontology of derivations
(derive ::partial-function :locus.set.logic.structure.protocols/structured-function)
(derive ::partial-transformation ::partial-function)
(derive ::partial-bijection ::partial-function)
(derive ::partial-permutation ::partial-transformation)
(derive ::partial-permutation ::partial-bijection)
(derive ::atomic-chart ::partial-permutation)
(derive PartialFunction ::partial-function)

; The defined domain is where the output of the partial function is not empty
(defmulti defined-domain type)

(defmethod defined-domain PartialFunction
  [^PartialFunction x]

  (.-domain x))

(defmethod defined-domain :locus.set.logic.structure.protocols/set-function
  [func]

  (inputs func))

; Convert partial functions to total functions
(defmethod to-function PartialFunction
  [func]

  (->SetFunction
    (multiselection (source-object func) #{0 1})
    (multiselection (target-object func) #{0 1})
    (fn [x]
      (if (empty? x)
        #{}
        (let [elem (first x)]
          (if ((defined-domain func) elem)
            #{(func elem)}
            #{}))))))

(defn partial-identity-function
  [coll]

  (PartialFunction. coll coll coll (fn [i] i)))

; Partial functions are structure copresheaves
(defmethod get-object PartialFunction
  [partial-function i]

  (case i
    0 (source-object partial-function)
    1 (target-object partial-function)))

(defmethod get-morphism PartialFunction
  [partial-function [a b]]

  (case [a b]
    [0 0] (partial-identity-function (source-object partial-function))
    [1 1] (partial-identity-function (target-object partial-function))
    [0 1] partial-function))

(defmethod get-set PartialFunction
  [partial-function i]

  (multiselection (get-object partial-function i) #{0 1}))

(defmethod get-function PartialFunction
  [partial-function i]

  (to-function (get-morphism partial-function i)))

; The two component functions of a partial function are the total component function
; and the inclusion function from the partial domain to the actual domain.
(defmulti total-component type)

(defmethod total-component ::partial-function
  [func]

  (SetFunction.
    (defined-domain func)
    (target-object func)
    (fn [i]
      (func i))))

(defmulti defined-domain-inclusion type)

(defmethod defined-domain-inclusion ::partial-function
  [func]

  (InclusionFunction.
    (defined-domain func)
    (source-object func)))

; Images generalised for partial functions
(defmulti partial-function-image type)

(defmethod partial-function-image :default
  [func]

  (set
    (map
      (fn [i]
        (func i))
      (defined-domain func))))

; Underlying relations for all partial functions
(defmethod underlying-relation ::partial-function
  [func]

  (set
    (map
      (fn [i]
        (list i (func i)))
      (defined-domain func))))

(defmethod visualize ::partial-function
  [rel]

  (let [p {0 (source-object rel)
           1 (target-object rel)}
        v (set
            (map
              (fn [[a b]]
                (list (list 0 a) (list 1 b)))
              (underlying-relation rel)))]
    (visualize-clustered-digraph* "LR" p v)))

(defmethod underlying-multirelation ::partial-function
  [func] (underlying-relation func))

; Every partial function can be defined by a triple
(defn partial-function-triple
  [func]

  (list (source-object func) (target-object func) (underlying-relation func)))

; Implementation of the category of partial functions
(defmethod compose* ::partial-function
  [a b]

  (let [new-defined-domain (set
                             (filter
                               (fn [i]
                                 (let [next-val (b i)]
                                   (boolean
                                     ((defined-domain a) next-val))))
                               (defined-domain b)))]
    (PartialFunction.
      new-defined-domain
      (source-object b)
      (target-object a)
      (fn [x]
        (a (b x))))))

; Partial functions also have set images
(defn partial-function-set-image
  [partial-function coll]

  (set
    (map
      partial-function
      (intersection (defined-domain partial-function) coll))))

(defn partial-function-set-inverse-image
  [partial-function coll]

  (set
    (filter
      (fn [in]
        (superset? (list (partial-function-set-image partial-function #{in}) coll)))
      (source-object partial-function))))

(defmethod image
  [::partial-function :locus.set.logic.core.set/universal]
  [func coll]

  (partial-function-set-image func coll))

(defmethod inverse-image
  [::partial-function :locus.set.logic.core.set/universal]
  [func coll]

  (partial-function-set-inverse-image func coll))

; Adjoin undefined inputs to a partial function
(defmethod adjoin-inputs ::partial-function
  [func coll]

  (PartialFunction.
    (defined-domain func)
    (union coll (source-object func))
    (target-object func)
    func))

(defmethod adjoin-outputs ::partial-function
  [func coll]

  (PartialFunction.
    (defined-domain func)
    (source-object func)
    (union coll (target-object func))
    func))

; Dual concepts of missing inputs and outputs exist for partial functions
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

; Empty partial functions have an empty defined domain
(defn empty-partial-function
  [source target]

  (PartialFunction.
    #{}
    source
    target
    (fn [x] x)))

; Relational partial functions
; This method turns a set of ordered pairs into a partial function
(defn binary-relation-triple
  [rel]

  (loop [coll (seq rel)
         in #{}
         out #{}
         mapping {}]
    (if (empty? coll)
      [in out mapping]
      (let [[a b] (first coll)]
        (recur
         (rest coll)
         (conj in a)
         (conj out b)
         (conj mapping [a b]))))))

(defn relational-partial-function
  [rel]

  (let [[in out mapping] (binary-relation-triple rel)]
    (PartialFunction.
      in
      in
      out
      mapping)))

; Conversion routines
; These methods convert various types of mathematical objects into partial functions.
(defmulti to-partial-function type)

(defmethod to-partial-function PartialFunction
  [func] func)

(defmethod to-partial-function IPersistentMap
  [coll]

  (let [in (set (keys coll))
        out (set (vals coll))]
    (PartialFunction. in in out coll)))

(defmethod to-partial-function :locus.set.logic.core.set/universal
  [coll] (relational-partial-function coll))

(defmethod to-partial-function :locus.set.logic.structure.protocols/set-function
  [func]

  (PartialFunction.
    (inputs func)
    (inputs func)
    (outputs func)
    (fn [x]
      (func x))))

(defmethod to-partial-function :default
  [func]

  (to-partial-function (underlying-function func)))

; Products and coproducts in the category of partial functions
(defmethod coproduct PartialFunction
  [& partial-functions]

  (->PartialFunction
    (apply coproduct (map defined-domain partial-functions))
    (apply coproduct (map source-object partial-functions))
    (apply coproduct (map target-object partial-functions))
    (fn [[i v]]
      (list i ((nth partial-functions i) v)))))

(defmethod product PartialFunction
  [& partial-functions]

  (->PartialFunction
    (apply product (map defined-domain partial-functions))
    (apply product (map source-object partial-functions))
    (apply product (map target-object partial-functions))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth partial-functions i) v))
        coll))))

; Ontology of partial functions
(defn partial-function?
  [x]

  (isa? (type x) ::partial-function))

(defmulti partial-transformation? type)

(defmethod partial-transformation? ::partial-transformation
  [x] true)

(defmethod partial-transformation? :default
  [x]

  (and
    (partial-function? x)
    (= (source-object x) (target-object x))))

(defmulti partial-bijection? type)

(defmethod partial-bijection? ::partial-bijection
  [x] true)

(defmethod partial-bijection? ::partial-function
  [x]

  (and
    (partial-function? x)
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
    (partial-function? x)
    (= (source-object x) (target-object x))
    (= (count (defined-domain x)) 1)))

; Ontology of partial functions not defined by core multimethods
(defn surjective-partial-function?
  [x]

  (and
    (partial-function? x)
    (empty? (missing-outputs x))))

(defn surjective-partial-bijection?
  [x]

  (and
    (partial-bijection? x)
    (empty? (missing-outputs x))))

(defn empty-partial-function?
  [x]

  (and
    (partial-function? x)
    (= (count (defined-domain x)) 0)))

(defn identity-partial-function?
  [x]

  (and
    (partial-function? x)
    (every?
      (fn [i]
        (= (x i) i))
      (defined-domain x))))

(defn identity-partial-permutation?
  [x]

  (and
    (identity-partial-function? x)
    (= (source-object x) (target-object x))))