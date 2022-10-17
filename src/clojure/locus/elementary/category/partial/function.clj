(ns locus.elementary.category.partial.function
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.inclusion.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.bijection.core.object Bijection)
           (clojure.lang PersistentArrayMap IPersistentMap)
           (locus.base.function.inclusion.object InclusionFunction)))

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

  StructuredDiset
  (first-set [this] source)
  (second-set [this] target)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Ontology of derivations
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

(defmethod defined-domain :locus.base.logic.structure.protocols/set-function
  [func]

  (inputs func))

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
  [func]

  (visualize (underlying-relation func)))

(defmethod underlying-multirelation ::partial-function
  [func] (underlying-relation func))

; Every partial function can be defined by a triple
(defn partial-function-triple
  [func]

  (list (source-object func) (target-object func) (underlying-relation func)))

; Category of partial functions
(defn partial-identity-function
  [coll]

  (PartialFunction. coll coll coll (fn [i] i)))

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

; Convert partial functions to image functions
(defmethod to-function ::partial-function
  [^PartialFunction func]

  (->ImageFunction
    (source-object func)
    (target-object func)
    (fn [x]
      (if ((defined-domain func) x)
        #{(func x)}
        #{}))))

; Empty partial functions have an empty defined domain
(defn empty-partial-function
  [source target]

  (PartialFunction.
    #{}
    source
    target
    (fn [x] x)))

; Relational partial functions
(defn relational-partial-function
  ([rel] (relational-partial-function (vertices rel) rel))
  ([coll rel]
   (->PartialFunction
     (relation-domain rel)
     (relation-domain rel)
     (relation-codomain rel)
     (fn [x]
       (call rel x)))))

; Conversion routines
(defmulti to-partial-function type)

(defmethod to-partial-function PartialFunction
  [func] func)

(defmethod to-partial-function IPersistentMap
  [coll]

  (let [in (set (keys coll))
        out (set (vals coll))]
    (PartialFunction. in in out coll)))

(defmethod to-partial-function :locus.base.logic.core.set/universal
  [coll] (relational-partial-function coll))

(defmethod to-partial-function :locus.base.logic.structure.protocols/set-function
  [func]

  (PartialFunction.
    (inputs func)
    (inputs func)
    (outputs func)
    (fn [x]
      (func x))))

(defmethod to-partial-function :locus.elementary.copresheaf.core.protocols/bijection
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