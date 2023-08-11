(ns locus.sub.reflective.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all]
            [dorothy.core :as dot]))

; These are objects in the topos of reflective subobjects, which is the most basic
; non-trivial example of a slice topos of a topos, constructed using the fundamental
; theorem of topos theory.

(deftype ReflectiveSubobject [coll parent]
  ConcreteObject
  (underlying-set [this]
    parent))

(derive ReflectiveSubobject :locus.sub.core.object/set-subalebra)

(defmethod included-elements ReflectiveSubobject
  [^ReflectiveSubobject obj]

  (.-coll obj))

; Create a reflective subobject by a certain pair of cardinalities
(defn make-reflective-subobject
  [n k]

  (ReflectiveSubobject.
    (set (range n))
    (set (range k))))

; Products and coproducts in the topos of reflective subobjects of functions
(defmethod coproduct ReflectiveSubobject
  [& sets]

  (->SetSubalgebra
    (apply coproduct (map included-elements sets))
    (apply coproduct (map underlying-set sets))))

(defmethod product ReflectiveSubobject
  [& sets]

  (let [false-elements (apply product (map excluded-elements sets))
        true-elements (apply product (map included-elements sets))]
    (ReflectiveSubobject.
      true-elements
      (union false-elements true-elements))))

(def reflective-subobject-of-truth-values
  (ReflectiveSubobject.
    '#{(0 1) (1 1)}
    '#{(0 0) (0 1) (1 0) (1 1)}))

; Ontology of reflective subobjects
(defn reflective-subobject?
  [obj]

  (= (type obj) ReflectiveSubobject))