(ns locus.set.square.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.mapping.effects.global.identity :refer :all]
            [locus.con.core.setpart :refer :all])
  (:import (locus.set.mapping.effects.global.identity IdentityFunction)
           (locus.set.mapping.general.core.object SetFunction)))

; Objects in the topos Sets^[1, {1,1} 1]
; A square is so called because when depicted its defining commutative diagram appears
; as a square. In other words, it is a copresheaf over the four element diamond shaped
; partial order. In this file, all relevant operations for objects of this topos
; like products and coproducts are defined and implemented.

; Objects in this topos have an additional characteristic, which is that they emerge from
; the morphisms in the topos of functions Sets^(->). Consequently, every diamond is
; defined so that has a source function and a target function. The subobject classifier
; and characteristic morphisms in the topos Sets^(->) are defined in this file and an
; ontology of diamonds is provided.

; Every morphism in a topos has an associated epi-mono factorisation. In the case of
; diamonds, which are like morphisms of functions, they have a function congruence
; for an epi part and a function subobject for a mono part. This corresponds to the
; partition kernel and set image of a function, which now occurs in pairs as every
; morphism of functions is defined over a pair of functions.

; The protocol of concrete higher morphism is used for structured diamonds
(defprotocol ConcreteHigherMorphism
  "Topos theoretic foundations often lead us to treat functions as objects in their own
  right. Further, we often have categories that are often a lot like categorise with additional
  structure. Corresponding to this, we generalize from categories of structured sets to categories
  of structured functions and we generalize from underlying functions to underlying morphisms
  of functions in the arrow topos of the topos of Sets."

  (underlying-morphism-of-functions [this]
    "Map a morphism of a category into a morphism in the topos of functions."))

; Objects in the topos Sets^[1, {1,1} 1]
(deftype SetSquare [source-function target-function input-function output-function]
  AbstractMorphism
  (source-object [this] source-function)
  (target-object [this] target-function)

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this] this)

  ConcreteMorphism
  (inputs [this] (underlying-set (source-object this)))
  (outputs [this] (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function)

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i 0) (list 0 (input-function v))
      (= i 1) (list 1 (output-function v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive SetSquare :locus.set.quiver.structure.core.protocols/set-square)

; Component arrows of diamonds
(defn input-set-function
  [^SetSquare diamond]

  (SetFunction.
    (inputs (source-object diamond))
    (inputs (target-object diamond))
    (.-input_function diamond)))

(defn output-set-function
  [^SetSquare diamond]

  (SetFunction.
    (outputs (source-object diamond))
    (outputs (target-object diamond))
    (.-output_function diamond)))

(defn common-composite-set-function
  [morphism]

  (compose (output-set-function morphism) (source-object morphism)))

; Component functions
(defn vertical-function
  [^SetSquare diamond, x]

  (case x
    0 (source-object diamond)
    1 (target-object diamond)))

(defn horizontal-function
  [^SetSquare diamond, x]

  (case x
    0 (input-set-function diamond)
    1 (output-set-function diamond)))

; Components of diamonds
(defmethod get-set SetSquare
  [diamond [i v]]

  (case i
    0 (get-set (source-object diamond) v)
    1 (get-set (target-object diamond) v)))

(defmethod get-function SetSquare
  [diamond [[i v] [j w]]]

  (case [i j]
    [0 0] (get-function (source-object diamond) [v w])
    [1 1] (get-function (target-object diamond) [v w])
    [0 1] (compose
            (get-function (target-object diamond) [v w])
            (horizontal-function diamond v))))

; Conversion multimethods
(defmulti to-set-square type)

(defmethod to-set-square SetSquare
  [diamond] diamond)

; Morphisms of functions especially useful in abstract algebra
(defn morphism-of-unary-operations
  [source target func]

  (->SetSquare
    source
    target
    func
    func))

(defn morphism-of-binary-operations
  [source target func]

  (->SetSquare
    source
    target
    (product func func)
    func))

(defn morphism-of-ternary-operations
  [source target func]

  (->SetSquare
    source
    target
    (product func func func)
    func))

(defn morphism-of-quaternary-operations
  [source target func]

  (->SetSquare
    source
    target
    (product func func func func)
    func))

; Algebraic homomorphisms in partial algebra
(defn morphism-of-partial-binary-operations
  [source target func]

  (->SetSquare
    source
    target
    (->SetFunction
      (inputs source)
      (outputs source)
      (fn [[a b]]
        (list (func a) (func b))))
    (->SetFunction
      (outputs source)
      (outputs target)
      func)))

; Special types of morphisms of functions
(defn constant-set-square
  [coll]

  (->SetSquare
    (identity-function coll)
    (identity-function coll)
    (identity-function coll)
    (identity-function coll)))

; Composition and identities in the topos of functions
(defmethod compose* SetSquare
  [f g]

  (SetSquare.
    (source-object g)
    (target-object f)
    (compose-functions (first-function f) (first-function g))
    (compose-functions (second-function f) (second-function g))))

(defn identity-set-square
  [f]

  (SetSquare.
    f
    f
    (IdentityFunction. (inputs f))
    (IdentityFunction. (outputs f))))

(defmethod identity-morphism SetFunction
  [func] (identity-set-square func))

; Diamonds are structured tetrasets
(defn source-input-set
  [diamond]

  (inputs (source-object diamond)))

(defn source-output-set
  [diamond]

  (outputs (source-object diamond)))

(defn target-input-set
  [diamond]

  (inputs (target-object diamond)))

(defn target-output-set
  [diamond]

  (outputs (target-object diamond)))

(defn set-square-quadruple
  [diamond]

  (list
    (source-input-set diamond)
    (source-output-set diamond)
    (target-input-set diamond)
    (target-output-set diamond)))

; Input and output action diamonds
(defn output-action-square
  [func output-action]

  (SetSquare.
    func
    (compose output-action func)
    (->IdentityFunction (inputs func))
    output-action))

(defn input-action-square
  [func input-action]

  (SetSquare.
    (compose func input-action)
    func
    input-action
    (->IdentityFunction (outputs func))))

; There are subalgebra and congruence components of morphisms of functions
; which can also be expressed as diamonds
(defn subalgebra-component
  [m]

  (list (function-image (first-function m))
        (function-image (second-function m))))

(defn congruence-component
  [m]

  (list (function-kernel (first-function m))
        (function-kernel (second-function m))))

(defn function-morphism-factorisation
  [m]

  (list (congruence-component m) (subalgebra-component m)))

; Get the dual of diamonds
(defn dual-set-square
  [morphism]

  (SetSquare.
    (input-set-function morphism)
    (output-set-function morphism)
    (source-object morphism)
    (target-object morphism)))

; Inclusion and quotient diamonds
(defn inclusion-square
  [f new-in new-out]

  (SetSquare.
    (subfunction f new-in new-out)
    f
    (SetFunction. new-in (inputs f) identity)
    (SetFunction. new-out (outputs f) identity)))

(defn projection-square
  [f in-partition out-partition]

  (SetSquare.
    f
    (quotient-function f in-partition out-partition)
    (projection-function in-partition)
    (projection-function out-partition)))

(defn element-square
  [f x]

  (let [out (f x)]
    (SetSquare.
      (pair-function x out)
      f
      (inclusion-function #{x} (inputs f))
      (inclusion-function #{out} (outputs f)))))

; Preservation and reflection methods
(defn set-pair-image
  [diamond [s t]]

  (let [h (first-function diamond)
        k (second-function diamond)]
    [(set-image h s)
     (set-image k t)]))

(defn set-pair-inverse-image
  [diamond [s t]]

  (let [h (first-function diamond)
        k (second-function diamond)]
    [(set-inverse-image h s)
     (set-inverse-image k t)]))

(defn partition-pair-image
  [diamond [p q]]

  (let [h (first-function diamond)
        k (second-function diamond)]
    [(partition-pair-image h p)
     (partition-pair-image k q)]))

(defn partition-pair-inverse-image
  [diamond [p q]]

  (let [h (first-function diamond)
        k (second-function diamond)]
    [(partition-pair-inverse-image h p)
     (partition-pair-inverse-image k q)]))

; Products and coproducts in the topos of diamonds
(defmethod product SetSquare
  [& diamonds]

  (SetSquare.
    (apply product (map source-object diamonds))
    (apply product (map target-object diamonds))
    (apply product (map input-set-function diamonds))
    (apply product (map output-set-function diamonds))))

(defmethod coproduct SetSquare
  [& diamonds]

  (SetSquare.
    (apply coproduct (map source-object diamonds))
    (apply coproduct (map target-object diamonds))
    (apply coproduct (map input-set-function diamonds))
    (apply coproduct (map output-set-function diamonds))))

; We need to create a subobject classifier for the topos of functions
(def truth-function
  (SetFunction.
    #{0 1/2 1}
    #{0 1}
    {0 0
     1/2 1
     1 1}))

(defn classify-functional-truth
  [func new-in new-out elem]

  (cond
    (contains? new-in elem) 1
    (contains? new-out (func elem)) 1/2
    :else 0))

(defn subfunction-input-classifier
  [func new-in new-out]

  (SetFunction.
    (inputs func)
    #{0 1/2 1}
    (fn [elem]
      (classify-functional-truth func new-in new-out elem))))

(defn subfunction-output-classifier
  [func new-in new-out]

  (SetFunction.
    (outputs func)
    #{0 1}
    (fn [elem]
      (if (contains? new-out elem)
        1
        0))))

(defn subfunction-character
  [func new-in new-out]

  (SetSquare.
    func
    truth-function
    (subfunction-input-classifier func new-in new-out)
    (subfunction-output-classifier func new-in new-out)))

; Internal hom in the topos Sets^(->)
; An evaluation arrow is associated to the internal hom in the topos Sets^(->) which
; is a morphism of functions from the internal hom object. This is also defined and described.
(defn in-function-hom?
  [func a b]

  (and
    (= (type func) SetSquare)
    (equal-functions? a (source-object func))
    (equal-functions? b (target-object func))))

(defn internal-function-hom
  [f g]

  (let [current-hom-class (->Universal
                            (fn [func]
                              (in-hom-class? func f g)))
        b (outputs f)
        d (outputs g)]
    (->SetFunction
      current-hom-class
      (internal-set-hom b d)
      (fn [morphism]
        (second-function morphism)))))

(defn function-ev
  [f g]

  (SetSquare.
    (product (internal-function-hom f g) f)
    g
    (fn [morphism x]
      ((first-function morphism) x))
    (fn [func x]
      (func x))))

; Subobjects in the topos of squares of sets
(defn subsquare?
  [diamond [first-new-in first-new-out] [second-new-in second-new-out]]

  (and
    (subfunction? (first-function diamond) first-new-in first-new-out)
    (subfunction? (second-function diamond) second-new-in second-new-out)
    (subfunction? (input-set-function diamond) first-new-in second-new-in)
    (subfunction? (output-set-function diamond) first-new-out second-new-out)))

(defn subsquare
  [diamond [first-new-in first-new-out] [second-new-in second-new-out]]

  (SetSquare.
    (subfunction (first-function diamond) first-new-in first-new-out)
    (subfunction (second-function diamond) second-new-in second-new-out)
    (subfunction (input-set-function diamond) first-new-in second-new-in)
    (subfunction (output-set-function diamond) first-new-out second-new-out)))

; Quotients in the topos of diamonds
(defn square-congruence?
  [diamond [in-partition1 out-partition1] [in-partition2 out-partition2]]

  (and
    (io-relation? (first-function diamond) in-partition1 out-partition1)
    (io-relation? (second-function diamond) in-partition2 out-partition2)
    (io-relation? (input-set-function diamond) in-partition1 in-partition2)
    (io-relation? (output-set-function diamond) out-partition1 out-partition2)))

(defn quotient-square
  [diamond [in-partition1 out-partition1] [in-partition2 out-partition2]]

  (SetSquare.
    (quotient-function (first-function diamond) in-partition1 out-partition1)
    (quotient-function (second-function diamond) in-partition2 out-partition2)
    (quotient-function (input-set-function diamond) in-partition1 in-partition2)
    (quotient-function (output-set-function diamond) out-partition1 out-partition2)))

; Validity test for diamonds
(defn valid-commutative-square?
  [m]

  (= (compose-functions (target-object m) (first-function m))
     (compose-functions (second-function m) (source-object m))))

; Ontology of diamonds
(defn set-square?
  [morphism]

  (= (type morphism) SetSquare))

(defn set-episquare?
  [morphism]

  (and
    (set-square? morphism)
    (surjective? (first-function morphism))
    (surjective? (second-function morphism))))

(defn set-monosquare?
  [morphism]

  (and
    (set-square? morphism)
    (injective? (first-function morphism))
    (injective? (second-function morphism))))

(defn set-isosquare?
  [morphism]

  (and
    (set-square? morphism)
    (invertible? (first-function morphism))
    (invertible? (second-function morphism))))

(defn inclusion-square?
  [morphism]

  (and
    (set-square? morphism)
    (inclusion-function? (first-function morphism))
    (inclusion-function? (second-function morphism))))

(defn identity-set-square?
  [morphism]

  (and
    (set-square? morphism)
    (identity-function? (first-function morphism))
    (identity-function? (second-function morphism))))

(defn input-action-set-square?
  [morphism]

  (and
    (set-square? morphism)
    (identity-function? (second-function morphism))))

(defn output-action-set-square?
  [morphism]

  (and
    (set-square? morphism)
    (identity-function? (first-function morphism))))

(defn set-endosquare?
  [morphism]

  (and
    (set-square? morphism)
    (equal-functions? (source-object morphism) (target-object morphism))))

(defn set-autosquare?
  [morphism]

  (and
    (set-isosquare? morphism)
    (equal-functions? (source-object morphism) (target-object morphism))))

(defn element-set-square?
  [morphism]

  (and
    (set-square? morphism)
    (ordered-pair-function? (source-object morphism))))

; Ontology of properties of diamonds
(defn !=set-square
  [a b]

  (and
    (set-square? a)
    (set-square? b)
    (not= a b)))

(defn !=set-square-vertical-source
  [a b]

  (and
    (set-square? a)
    (set-square? b)
    (not= (source-object a) (source-object b))))

(defn !=set-square-vertical-target
  [a b]

  (and
    (set-square? a)
    (set-square? b)
    (not= (target-object a) (target-object b))))

(defn !=set-square-horizontal-source
  [a b]

  (and
    (set-square? a)
    (set-square? b)
    (not= (input-set-function a) (input-set-function b))))

(defn !=set-square-horizontal-target
  [a b]

  (and
    (set-square? a)
    (set-square? b)
    (not= (output-set-function a) (output-set-function b))))

; Visualisation of diamond copresheaves
(defmethod visualize SetSquare
  [^SetSquare diamond]

  (let [[p v] (generate-copresheaf-data
                {0 (source-input-set diamond)
                 1 (source-output-set diamond)
                 2 (target-input-set diamond)
                 3 (target-output-set diamond)}
                #{(list 0 1 (source-object diamond))
                  (list 2 3 (target-object diamond))
                  (list 0 2 (first-function diamond))
                  (list 1 3 (second-function diamond))})]
    (visualize-clustered-digraph* "BT" p v)))

