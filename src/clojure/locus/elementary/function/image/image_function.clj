(ns locus.elementary.function.image.image-function
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.function.set-valued.set-valued-function :refer :all])
  (:import (locus.elementary.logic.base.core PowerSet)))

; Image functions are complete union homomorphisms of power sets
; They are equivalent to set relations in the category Rel. In other words, we can consider Rel to be the subcategory
; of the topos Sets consisting of image functions. An image function is defined by the datum of a multi-valued
; function between two sets. The image function can be applied to sets of elements, after which it will produce
; the union of all applications of singletons of the set. As a result, image functions can also be considered to
; be complete union homomorphisms of power sets.
(deftype ImageFunction [source target func]
  StructuredDiset
  (first-set [this]
    (PowerSet. source))
  (second-set [this]
    (PowerSet. target))

  AbstractMorphism
  (source-object [this] (first-set this))
  (target-object [this] (second-set this))

  ConcreteMorphism
  (inputs [this] (first-set this))
  (outputs [this] (second-set this))

  clojure.lang.IFn
  (invoke [this obj]
    (apply union (map func obj)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ImageFunction :locus.elementary.function.core.protocols/set-function)

; Image and inverse image functions
(defn image-function
  [func]

  (ImageFunction.
    (inputs func)
    (outputs func)
    (fn [x]
      (set-image func #{x}))))

(defn inverse-image-function
  [func]

  (ImageFunction.
    (inputs func)
    (outputs func)
    (fn [x]
      (set-inverse-image func #{x}))))

; The subcategory of image functions is isomorphic to Rel
(defmethod compose* ImageFunction
  [a b]

  (ImageFunction.
    (source-object b)
    (target-object a)
    (fn [x]
      (apply union (map a (b x))))))

; Get a set-valued function from the singletons of the image function
(defn singleton-images-function
  [^ImageFunction func]

  (->SetValuedFunction
    (.source func)
    (.target func)
    (.func func)))

; Ontology of image functions
(defmulti image-function? type)

(defmethod image-function? ImageFunction
  [func] true)

(defmethod image-function? :locus.elementary.function.core.protocols/set-function
  [func]

  (and
    (power-set? (inputs func))
    (power-set? (outputs func))
    (every?
      (fn [coll]
        (equal-universals?
          (func coll)
          (apply
            union
            (map
              (fn [i]
                (func #{i}))
              coll))))
      (inputs func))))

(defmethod image-function? :default
  [func] false)

