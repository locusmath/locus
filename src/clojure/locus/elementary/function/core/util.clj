(ns locus.elementary.function.core.util
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all])
  (:import [locus.elementary.function.core.object SetFunction]
           [locus.elementary.relation.binary.product BinaryCartesianProduct]))

; This contains a variety of utility functions which are not related to the core system of functionality
; needed to implement the topos of functions Sets^(->). In particular, this contains a number
; of utility functions that create set functions from various data structures.

; We can create a number of utility functions that can be 
; used to create functions.
(defn pair-function
  [a b]

  (SetFunction.
   #{a}
   #{b}
   (constantly b)))

(defn loop-function
  [a]

  (SetFunction. #{a} #{a} identity))

(defn element-function
  [elem coll]

  (SetFunction. #{elem} coll identity))

(defn constant-function
  [coll value]

  (SetFunction.
   coll
   #{value}
   (fn [i]
     value)))

; Point function
(defn point-function
  [coll point]

  (SetFunction. '#{()} coll (fn [i] point)))

; Inverting functions as if they were bijections
(defn invert-function
  [func]

  (SetFunction.
    (outputs func)
    (inputs func)
    (fn [i]
      (first (set-inverse-image func #{i})))))

; There are special techniques that we have for dealing with inclusion functions
(def not-function
  (SetFunction.
   #{false true}
   #{false true}
   not))

(defn complement-characteristic-function
  [func]

  (compose-functions not-function func))

; We can use the definition of embedded relations in order to create
; special functions associated with them.
(defn empty-inclusion-function
  [coll]

  (inclusion-function #{} coll))

(defn embedded-relation
  [rel in out]

  (inclusion-function rel (BinaryCartesianProduct. in out)))

(defn embeddify-relation
  [rel]

  (embedded-relation rel (relation-domain rel) (relation-codomain rel)))

(defn embeddify-family
  [family]

  (inclusion-function family (->PowerSet (apply union family))))

(defn underlying-embedded-relation-of-function
  [func]

  (embedded-relation
   (underlying-relation func)
   (inputs func)
   (outputs func)))

(defn embedded-function-image
  [func]

  (inclusion-function (function-image func) (outputs func)))

(defn embedded-image
  [func coll]

  (inclusion-function (set-image func coll) (outputs func)))

(defn embedded-inverse-image
  [func coll]

  (inclusion-function (set-inverse-image func coll) (inputs coll)))

; Concatenate functions together
(defn concat-functions
  "These functions need to have a common input"
  [& functions]

  (when (not (empty? functions))
    (SetFunction.
     (inputs (first functions))
     (apply cartesian-product (map outputs functions))
     (fn [x]
       (map (fn [f] (f x)) functions)))))

; Projection functions of products
(defn first-projection
  [a b]

  (SetFunction.
   (cartesian-product a b)
   a
   (fn [[a b]] a)))

(defn second-projection
  [a b]

  (SetFunction.
   (cartesian-product a b)
   b
   (fn [[a b]] b)))

(defn nth-projection
  [coll i]

  (SetFunction.
   (apply cartesian-product coll)
   (nth coll i)
   (fn [arg] (nth arg i))))

; Inclusion functions corresponding to coproducts
(defn first-inclusion
  [a b]

  (inclusion-function
   (map #(list 0 %) a)
   (cartesian-coproduct a b)))

(defn second-inclusion
  [a b]

  (inclusion-function
   (map #(list 1 %) b)
   (cartesian-coproduct a b)))

(defn nth-inclusion
  [coll i]

  (inclusion-function
   (map #(list i %) (nth coll i))
   (apply cartesian-coproduct coll)))
