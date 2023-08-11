(ns locus.sub.reflective.arrow
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.function.inclusion.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all]
            [locus.sub.mapping.function :refer :all]
            [locus.sub.reflective.object :refer :all]
            [dorothy.core :as dot])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; Morphisms in the category of reflective subobjects. These are also the reflective
; subobjects in the topos of functions, and the fixed points of the double
; negation topology. At the same time, these are morphisms in a slice topos over
; the topos of sets.
(deftype ReflectiveSubfunction [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this obj]
    (func obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ReflectiveSubfunction :locus.sub.mapping.function/set-subfunction)

; A constructor for reflective subobjects of functions
(defn reflective-subfunction
  [func output-elements]

  (let [in-elements (set-inverse-image func output-elements)
        in-object (->ReflectiveSubobject in-elements (inputs func))
        out-object (->ReflectiveSubobject output-elements (outputs func))]
    (->ReflectiveSubfunction in-object out-object func)))
