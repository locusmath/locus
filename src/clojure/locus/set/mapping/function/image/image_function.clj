(ns locus.set.mapping.function.image.image-function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.function.set-valued.set-valued-function :refer :all]))

; Image functions are complete union homomorphisms of power sets
; They are equivalent to set relations in the category Rel. In other words, we can consider Rel to be the subcategory
; of the topos Sets consisting of image functions. An image function is defined by the datum of a multi-valued
; function between two sets. The image function can be applied to sets of elements, after which it will produce
; the union of all applications of singletons of the set. As a result, image functions can also be considered to
; be complete union homomorphisms of power sets.
(deftype ImageFunction [source target func]
  ConcreteMorphism
  (inputs [this]
    (->PowerSet source))
  (outputs [this]
    (->PowerSet target))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this obj]
    (apply union (map func obj)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ImageFunction :locus.set.logic.structure.protocols/set-function)

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


