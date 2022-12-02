(ns locus.quiver.diset.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.diset.core.object :refer :all])
  (:import (locus.quiver.diset.core.object Diset)))

; Objects in the topos Sets^{2+2}
; A difunction is equivalent to a pair of functions. It can be defined as a copresheaf
; over the index category 2+2, and therefore it is an object of a topos. We apply
; all the common topos theoretic constructions like subobjects, quotients, products,
; coproducts, etc to difunctions by doubling up their counterparts in functions.
(deftype Difunction [f g]
  StructuredDifunction
  (first-function [this] f)
  (second-function [this] g)

  AbstractMorphism
  (source-object [this]
    (Diset. (inputs f) (inputs g)))
  (target-object [this]
    (Diset. (outputs f) (outputs g)))

  ConcreteMorphism
  (inputs [this]
    (underlying-set (source-object this)))
  (outputs [this]
    (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i 0) (list 0 (f v))
      (= i 1) (list 1 (g v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Difunction :locus.quiver.base.core.protocols/difunction)

; Components of difunctions
(defmethod get-set Difunction
  [difunction [i v]]

  (case [i v]
    [0 0] (first-set (source-object difunction))
    [0 1] (second-set (source-object difunction))
    [1 0] (first-set (target-object difunction))
    [1 1] (second-set (target-object difunction))))

(defmethod get-function Difunction
  [difunction [[i v] [j w]]]

  (case [[i v] [j w]]
    [[0 0] [0 0]] (identity-function (first-set (source-object difunction)))
    [[0 1] [0 1]] (identity-function (second-set (source-object difunction)))
    [[1 0] [1 0]] (identity-function (first-set (target-object difunction)))
    [[1 1] [1 1]] (identity-function (second-set (target-object difunction)))
    [[0 0] [1 0]] (first-function difunction)
    [[0 1] [1 1]] (second-function difunction)))

; Difunction applications
(defn first-apply
  [func x]

  ((first-function func) x))

(defn second-apply
  [func x]

  ((second-function func) x))

; Convert a difunction into a coproduct function
(defmethod to-function Difunction
  [^Difunction func]

  (->CoproductFunction [(.-f func) (.-g func)]))

; Conversion mechanisms for converting structures to pairs of functions
(defmulti to-difunction type)

(defmethod to-difunction Difunction
  [^Difunction difunc] difunc)

; Difunction builders
(defn difunction
  ([obj]
   (if (or (vector? obj) (seq? obj))
     (Difunction. (first obj) (second obj))
     (Difunction. (first-function obj) (second-function obj))))
  ([a b]
   (Difunction. a b)))

(defn underlying-difunction
  [morphism]

  (Difunction.
    (first-function morphism)
    (second-function morphism)))

; Composition and identities in the topos difunctions
(defmethod compose* Difunction
  [a b]

  (Difunction.
    (compose-functions (first-function a) (first-function b))
    (compose-functions (second-function a) (second-function b))))

(defn identity-difunction
  [pair]

  (Difunction.
    (identity-function (first-set pair))
    (identity-function (second-set pair))))

(defmethod identity-morphism Diset
  [pair] (identity-difunction pair))

; Equal difunctions having the same first and second parts
(defn equal-difunction
  [func]

  (Difunction. func func))

; Inclusion and projection pairs used for building difunctions
(defn inclusion-difunction
  [pair new-in new-out]

  (Difunction.
    (inclusion-function new-in (first-set pair))
    (inclusion-function new-out (second-set pair))))

(defn projection-difunction
  [pair in-partition out-partition]

  (Difunction.
    (projection-function in-partition)
    (projection-function out-partition)))

; Product and coproduct of the component functions of a difunction
(defn function-component-coproduct
  [difunction]

  (coproduct (first-function difunction) (second-function difunction)))

(defn function-component-product
  [difunction]

  (product (first-function difunction) (second-function difunction)))

; Epi mono factorisation in the topos of difunctoins
(defn function-kernel-pair
  [morphism]

  (list (function-kernel (first-function morphism))
        (function-kernel (second-function morphism))))

(defn function-image-pair
  [morphism]

  (list (function-image (first-function morphism))
        (function-image (second-function morphism))))

(defn difunction-kernel-image-factorisation
  [morphism]

  (list (function-kernel-pair morphism) (function-image-pair morphism)))

; Images over disets for difunctions
(defn difunction-image
  [^Difunction func, ^Diset coll]

  (->Diset
    (first-apply func (first-set coll))
    (second-apply func (second-set coll))))

(defn difunction-inverse-image
  [^Difunction func, ^Diset coll]

  (->Diset
    (first-apply func (first-set coll))
    (second-apply func (second-set coll))))

; Subobject classifiers for disets
(def truth-diset
  (Diset. #{false true} #{false true}))

(defn subdiset-character
  [pair new-in new-out]

  (Difunction.
    (subset-character new-in (first-set pair))
    (subset-character new-out (second-set pair))))

; Joining pairs of pairs of sets
(defn join-pair-of-set-pairs
  [& args]

  (list
    (apply join-set-pairs (map first args))
    (apply meet-set-pairs (map second args))))

(defn meet-pair-of-set-pairs
  [& args]

  (list
    (apply meet-set-pairs (map first args))
    (apply meet-set-pairs (map second args))))

; Products and coproducts in the topos of difunctions
(defn difunction-product
  [& pairs]

  (Difunction.
    (apply function-product (map first-function pairs))
    (apply function-product (map second-function pairs))))

(defn difunction-coproduct
  [& pairs]

  (Difunction.
    (apply function-coproduct (map first-function pairs))
    (apply function-coproduct (map second-function pairs))))

(defmethod product Difunction
  [& args]

  (apply difunction-product args))

(defmethod coproduct Difunction
  [& args]

  (apply difunction-coproduct args))

; Operations for getting subobjects of difunctions
(defn restrict-first-function
  [difunction coll]

  (Difunction.
    (restrict-function (first-function difunction) coll)
    (second-function difunction)))

(defn restrict-second-function
  [difunction coll]

  (Difunction.
    (first-function difunction)
    (restrict-function (second-function difunction) coll)))

(defn restrict-difunction
  [difunction diset]

  (Difunction.
    (restrict-function (first-function difunction) (first-set diset))
    (restrict-function (second-function difunction) (second-set diset))))

(defn reduce-first-function
  [difunction new-in new-out]

  (Difunction.
    (subfunction (first-function difunction) new-in new-out)
    (second-function difunction)))

(defn reduce-second-function
  [difunction new-in new-out]

  (Difunction.
    (first-function difunction)
    (subfunction (second-function difunction) new-in new-out)))

(defn subdifunction
  [difunction [a c] [b d]]

  (Difunction.
    (subfunction (first-function difunction) a b)
    (subfunction (second-function difunction) c d)))

; Ontology of subdifunctions
(defn subdifunction?
  [difunction [a c] [b d]]

  (and
    (subfunction? (first-function difunction) a b)
    (subfunction? (second-function difunction) c d)))

(defn subdifunction-closure
  [difunction [a c] [b d]]

  (list
    (list a (union c (set-image (first-function difunction) a)))
    (list b (union d (set-image (second-function difunction) b)))))

; Enumeration of subobjects of difunctions
(defn subdifunctions
  [difunction]

  (set
    (cartesian-product
      (all-subalgebras (first-function difunction))
      (all-subalgebras (second-function difunction)))))

; Get the quotients of difunctions
(defn quotient-first-function
  [difunction in-partition out-partition]

  (Difunction.
    (quotient-function (first-function difunction) in-partition out-partition)
    (second-function difunction)))

(defn quotient-second-function
  [difunction in-partition out-partition]

  (Difunction.
    (first-function difunction)
    (quotient-function (second-function difunction) in-partition out-partition)))

(defn quotient-difunction
  [difunction [partition1 partition2] [partition3 partition4]]

  (Difunction.
    (quotient-function (first-function difunction) partition1 partition3)
    (quotient-function (second-function difunction) partition2 partition4)))

; Test for congruences of difunctions
(defn difunction-congruence?
  [difunction [partition1 partition2] [partition3 partition4]]

  (and
    (io-relation? (first-function difunction) partition1 partition3)
    (io-relation? (second-function difunction) partition2 partition4)))

(defn difunction-congruence-closure
  [difunction [partition1 partition2] [partition3 partition4]]

  (list
    (list
      partition1
      (join-set-partitions partition2 (partition-image (first-function difunction) partition1)))
    (list
      partition3
      (join-set-partitions partition4 (partition-image (second-function difunction) partition3)))))

; The congruence lattices of difunctions
(defn difunction-congruences
  [difunction]

  (set
    (cartesian-product
      (all-congruences (first-function difunction))
      (all-congruences (second-function difunction)))))

; Special classes of difunctions
(defn difunction?
  [pair]

  (= (type pair) Difunction))

(defn injective-difunction?
  [pair]

  (and
    (difunction? pair)
    (injective? (first-function pair))
    (injective? (second-function pair))))

(defn surjective-difunction?
  [pair]

  (and
    (difunction? pair)
    (surjective? (first-function pair))
    (surjective? (second-function pair))))

(defn invertible-difunction?
  [pair]

  (and
    (difunction? pair)
    (invertible? (first-function pair))
    (invertible? (second-function pair))))

(defn identity-difunction?
  [pair]

  (and
    (difunction? pair)
    (identity-function? (first-function pair))
    (identity-function? (second-function pair))))

(defn inclusion-difunction?
  [pair]

  (and
    (difunction? pair)
    (inclusion-function? (first-function pair))
    (inclusion-function? (second-function pair))))

(defn endo-difunction?
  [pair]

  (and
    (difunction? pair)
    (= (source-object pair) (target-object pair))))

(defn auto-difunction?
  [pair]

  (and
    (invertible-difunction? pair)
    (= (source-object pair) (target-object pair))))

(defn element-difunction?
  [pair]

  (and
    (difunction? pair)
    (let [src (source-object pair)]
      (and
        (singular-universal? (first-set src))
        (singular-universal? (second-set src))))))

; Equality conditions by properties of the two functions
(defn common-input-difunction?
  [difunction]

  (and
    (difunction? difunction)
    (= (inputs (first-function difunction)) (inputs (second-function difunction)))))

(defn common-output-difunction?
  [difunction]

  (and
    (difunction? difunction)
    (= (outputs (second-function difunction)) (outputs (second-function difunction)))))

(defn parallel-difunction?
  [difunction]

  (and
    (difunction? difunction)
    (= (inputs (first-function difunction)) (inputs (second-function difunction)))
    (= (outputs (first-function difunction)) (outputs (second-function difunction)))))

(defn equal-difunction?
  [difunction]

  (and
    (difunction? difunction)
    (equal-functions? (first-function difunction) (second-function difunction))))

; Ontology of properties of difunctions
(defn !=difunction
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= a b)))

(defn !=first-function
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (first-function a) (first-function b))))

(defn !=second-function
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (second-function a) (second-function b))))

(defn !=first-inputs
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (inputs (first-function a)) (inputs (first-function b)))))

(defn !=second-inputs
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (inputs (second-function a)) (inputs (second-function b)))))

(defn !=first-outputs
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (outputs (first-function a)) (outputs (first-function b)))))

(defn !=second-outputs
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (outputs (second-function a)) (outputs (second-function b)))))

(defn !=source-diset
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (source-object a) (source-object b))))

(defn !=target-diset
  [a b]

  (and
    (difunction? a)
    (difunction? b)
    (not= (target-object a) (target-object b))))

; A visualisation routine for difunctions as dependency functors
(defmethod visualize :locus.quiver.base.core.protocols/morphism-of-nary-quivers
  [difunction]

  (let [[p t] (generate-copresheaf-data
                {0 (inputs (first-function difunction))
                 1 (outputs (first-function difunction))
                 2 (inputs (second-function difunction))
                 3 (outputs (second-function difunction))}
                #{(list 0 1 (first-function difunction))
                  (list 2 3 (second-function difunction))})]
    (visualize-clustered-digraph* "BT" p t)))
