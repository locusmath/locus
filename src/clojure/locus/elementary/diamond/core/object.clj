(ns locus.elementary.diamond.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.elementary.function.inclusion.identity :refer :all]
            [locus.elementary.incidence.core.object :refer :all]
            [locus.elementary.cospan.core.object :refer :all])
  (:import [locus.elementary.function.core.object SetFunction]
           (locus.elementary.function.inclusion.identity IdentityFunction)
           (locus.elementary.incidence.core.object Span)
           (locus.elementary.cospan.core.object Cospan)))

; Objects in the topos Sets^[1, {1,1} 1]
; A diamond is so called because when depicted its defining commutative diagram appears
; as a diamond. In other words, it is a copresheaf over the four element diamond shaped
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

; Objects in the topos Sets^[1, {1,1} 1]
(deftype Diamond [source-function target-function input-function output-function]
  AbstractMorphism
  (source-object [this] source-function)
  (target-object [this] target-function)

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this] this)

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function))

(derive Diamond :locus.elementary.function.core.protocols/diamond)

; Validity test for diamonds
(defn valid-diamond?
  [m]

  (= (compose-functions (target-object m) (first-function m))
     (compose-functions (second-function m) (source-object m))))

; Composition and identities in the topos of functions
(defmethod compose* Diamond
  [f g]

  (Diamond.
    (source-object g)
    (target-object f)
    (compose-functions (first-function f) (first-function g))
    (compose-functions (second-function f) (second-function g))))

(defn identity-diamond
  [f]

  (Diamond.
    f
    f
    (IdentityFunction. (inputs f))
    (IdentityFunction. (outputs f))))

(defmethod identity-morphism SetFunction
  [func] (identity-diamond func))

; Diamonds are structured tetrasets
(defn source-input-set
  [diamond]

  (inputs (source-object diamond)))

(defn target-input-set
  [diamond]

  (inputs (target-object diamond)))

(defn source-output-set
  [diamond]

  (outputs (target-object diamond)))

(defn target-output-set
  [diamond]

  (outputs (target-object diamond)))

(defn diamond-quadruple
  [diamond]

  (list
    (source-input-set diamond)
    (source-output-set diamond)
    (target-input-set diamond)
    (target-output-set diamond)))

; These methods ensure that we can handle the first and second functions by
; using the topos of functions and the methods of categorical logic.
(defn input-set-function
  [morphism]

  (SetFunction.
    (inputs (source-object morphism))
    (inputs (target-object morphism))
    (.input_function morphism)))

(defn output-set-function
  [morphism]

  (SetFunction.
    (outputs (source-object morphism))
    (outputs (target-object morphism))
    (.output_function morphism)))

(defn common-composite-set-function
  [morphism]

  (compose (output-set-function morphism) (first-function morphism)))

; The upper cospan and the lower span in the topos Sets^[1,2,1]
; relates it to te topoi Sets^[1,2] and Sets^[2,1]
(defn upper-cospan
  [func]

  (cospan
    (second-function func)
    (target-object func)))

(defn lower-span
  [func]

  (span
    (first-function func)
    (source-object func)))

; The cartias diamond of a cospan copresheaf
(defn cartesian-diamond
  [^Cospan cospan]

  (let [cospan1 (first-cospan-function cospan)
        cospan2 (second-cospan-function cospan)
        [predecessor1 predecessor2] (fiber-product-projections cospan1 cospan2)]
    (Diamond.
      predecessor1
      cospan2
      predecessor1
      cospan1)))

; A cocartesian diamond of a span copresheaf
(defn cocartesian-diamond
  [^Span span]

  (let [span1 (edge-function span)
        span2 (vertex-function span)
        [successor1 successor2] (fiber-coproduct-projections span1 span2)]
    (Diamond.
      span1
      successor2
      span2
      successor1)))

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
(defn dual-diamond
  [morphism]

  (Diamond.
    (input-set-function morphism)
    (output-set-function morphism)
    (source-object morphism)
    (target-object morphism)))

; Inclusion and quotient diamonds
(defn inclusion-diamond
  [f new-in new-out]

  (Diamond.
    f
    (subfunction f new-in new-out)
    (SetFunction. new-in (inputs f) identity)
    (SetFunction. new-out (outputs f) identity)))

(defn projection-diamond
  [f in-partition out-partition]

  (Diamond.
    f
    (quotient-function f in-partition out-partition)
    (projection-function in-partition)
    (projection-function out-partition)))

(defn element-diamond
  [f x]

  (let [out (f x)]
    (Diamond.
      (pair-function x out)
      f
      (inclusion-function #{x} (inputs f))
      (inclusion-function #{out} (outputs f)))))

; Input and output actions
(defn output-action-diamond
  [func output-action]

  (Diamond.
    func
    (compose output-action func)
    (->IdentityFunction (inputs func))
    output-action))

(defn input-action-diamond
  [func input-action]

  (Diamond.
    (compose func input-action)
    func
    input-action
    (->IdentityFunction (outputs func))))

; Products and coproducts in the topos of diamonds
(defmethod product Diamond
  [& diamonds]

  (Diamond.
    (apply product (map source-object diamonds))
    (apply product (map target-object diamonds))
    (apply product (map input-set-function diamonds))
    (apply product (map output-set-function diamonds))))

(defmethod coproduct Diamond
  [& diamonds]

  (Diamond.
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

  (Diamond.
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
    (= (type func) Diamond)
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

  (Diamond.
    (product (internal-function-hom f g) f)
    g
    (fn [morphism x]
      ((first-function morphism) x))
    (fn [func x]
      (func x))))

; Subobjects in the topos of diamonds
(defn subdiamond?
  [diamond [first-new-in first-new-out] [second-new-in second-new-out]]

  (and
    (subfunction? (first-function diamond) first-new-in first-new-out)
    (subfunction? (second-function diamond) second-new-in second-new-out)
    (subfunction? (input-set-function diamond) first-new-in second-new-in)
    (subfunction? (output-set-function diamond) first-new-out second-new-out)))

(defn subdiamond
  [diamond [first-new-in first-new-out] [second-new-in second-new-out]]

  (Diamond.
    (subfunction (first-function diamond) first-new-in first-new-out)
    (subfunction (second-function diamond) second-new-in second-new-out)
    (subfunction (input-set-function diamond) first-new-in second-new-in)
    (subfunction (output-set-function diamond) first-new-out second-new-out)))

; Quotients in the topos of diamonds
(defn diamond-congruence?
  [diamond [in-partition1 out-partition1] [in-partition2 out-partition2]]

  (and
    (io-relation? (first-function diamond) in-partition1 out-partition1)
    (io-relation? (second-function diamond) in-partition2 out-partition2)
    (io-relation? (input-set-function diamond) in-partition1 in-partition2)
    (io-relation? (output-set-function diamond) out-partition1 out-partition2)))

(defn quotient-diamond
  [diamond [in-partition1 out-partition1] [in-partition2 out-partition2]]

  (Diamond.
    (quotient-function (first-function diamond) in-partition1 out-partition1)
    (quotient-function (second-function diamond) in-partition2 out-partition2)
    (quotient-function (input-set-function diamond) in-partition1 in-partition2)
    (quotient-function (output-set-function diamond) out-partition1 out-partition2)))

; Ontology of diamonds
(defn diamond?
  [morphism]

  (= (type morphism) Diamond))

(defn epidiamond?
  [morphism]

  (and
    (diamond? morphism)
    (surjective? (first-function morphism))
    (surjective? (second-function morphism))))

(defn monodiamond?
  [morphism]

  (and
    (diamond? morphism)
    (injective? (first-function morphism))
    (injective? (second-function morphism))))

(defn isodiamond?
  [morphism]

  (and
    (diamond? morphism)
    (invertible? (first-function morphism))
    (invertible? (second-function morphism))))

(defn inclusion-diamond?
  [morphism]

  (and
    (diamond? morphism)
    (inclusion-function? (first-function morphism))
    (inclusion-function? (second-function morphism))))

(defn identity-diamond?
  [morphism]

  (and
    (diamond? morphism)
    (identity-function? (first-function morphism))
    (identity-function? (second-function morphism))))

(defn input-action-diamond?
  [morphism]

  (and
    (diamond? morphism)
    (identity-function? (second-function morphism))))

(defn output-action-diamond?
  [morphism]

  (and
    (diamond? morphism)
    (identity-function? (first-function morphism))))

(defn endodiamond?
  [morphism]

  (and
    (diamond? morphism)
    (equal-functions? (source-object morphism) (target-object morphism))))

(defn autodiamond?
  [morphism]

  (and
    (isodiamond? morphism)
    (equal-functions? (source-object morphism) (target-object morphism))))

(defn element-diamond?
  [morphism]

  (and
    (diamond? morphism)
    (ordered-pair-function? (source-object morphism))))

; Ontology of properties of diamonds
(defn !=diamond
  [a b]

  (and
    (diamond? a)
    (diamond? b)
    (not= a b)))

(defn !=diamond-source-function
  [a b]

  (and
    (diamond? a)
    (diamond? b)
    (not= (source-object a) (source-object b))))

(defn !=diamond-target-function
  [a b]

  (and
    (diamond? a)
    (diamond? b)
    (not= (target-object a) (target-object b))))

(defn !=diamond-input-function
  [a b]

  (and
    (diamond? a)
    (diamond? b)
    (not= (input-set-function a) (input-set-function b))))

(defn !=diamond-output-function
  [a b]

  (and
    (diamond? a)
    (diamond? b)
    (not= (output-set-function a) (output-set-function b))))






