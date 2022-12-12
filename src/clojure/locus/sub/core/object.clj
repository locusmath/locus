(ns locus.sub.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.function.inclusion.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [dorothy.core :as dot])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; Objects in the category of sets with unary relations on them. Given a set S a unary relation R
; on S is equivalent to a subset of S.
(deftype SetSubalgebra [coll parent]
  ConcreteObject
  (underlying-set [this] parent))

(derive ::set-subalebra :locus.set.logic.structure.protocols/structured-set)
(derive SetSubalgebra ::set-subalebra)

; Included and excluded elements of subalgebras of sets
(defmulti included-elements type)

(defmethod included-elements SetSubalgebra
  [^SetSubalgebra coll]

  (.-coll coll))

(defn excluded-elements
  [coll]

  (difference (underlying-set coll) (included-elements coll)))

; A constructor for set subalgebras
(defn set-subalgebra
  [a b]

  (SetSubalgebra. a b))

; Empty and full set subalgebras
(defn full-set-subalgebra
  [coll]

  (SetSubalgebra. coll coll))

(defn empty-set-subalgebra
  [coll]

  (SetSubalgebra. #{} coll))

; Subalgebras form a category that admits complementation on objects
(defn complement-set-subalgebra
  [coll]

  (->SetSubalgebra
    (difference (underlying-set coll) (included-elements coll))
    (underlying-set coll)))

; Get subobject for a presheaf of unary relations
(defmulti get-subobject type)

(defmethod get-subobject ::set-subalebra
  [coll]

  (included-elements coll))

; Conversion routines to turn subsets into inclusion functions
(defmethod to-function SetSubalgebra
  [set-subalgebra]

  (->InclusionFunction (included-elements set-subalgebra) (underlying-set set-subalgebra)))

; Conversion routines for set subalgebras
(defmulti to-set-subalgebra type)

(defmethod to-set-subalgebra SetSubalgebra
  [^SetSubalgebra subalgebra] subalgebra)

(defmethod to-set-subalgebra :locus.set.logic.structure.protocols/inclusion-function
  [func]

  (SetSubalgebra. (inputs func) (outputs func)))

(defmethod to-set-subalgebra :locus.set.logic.core.set/universal
  [coll]

  (full-set-subalgebra coll))

; Product and coproducts of set subalgebras
(defmethod product ::set-subalebra
  [& sets]

  (->SetSubalgebra
    (apply product (map included-elements sets))
    (apply product (map underlying-set sets))))

(defmethod coproduct ::set-subalebra
  [& sets]

  (->SetSubalgebra
    (apply coproduct (map included-elements sets))
    (apply coproduct (map underlying-set sets))))

; Images and inverse images for set subalgebras
(defmethod image
  [:locus.set.logic.structure.protocols/set-function ::set-subalebra]
  [func coll]

  (->SetSubalgebra
    (set-image func (included-elements coll))
    (outputs func)))

(defmethod inverse-image
  [:locus.set.logic.structure.protocols/set-function ::set-subalebra]
  [func coll]

  (->SetSubalgebra
    (set-inverse-image func (included-elements coll))
    (inputs func)))

; Ontology of set subalgebras
(defmulti set-subalgebra? type)

(defmethod set-subalgebra? ::set-subalebra
  [subalgebra] true)

(defmethod set-subalgebra? :default
  [obj] false)

(defn empty-set-subalgebra?
  [obj]

  (and
    (set-subalgebra? obj)
    (empty? (included-elements obj))))

(defn full-set-subalgebra?
  [obj]

  (and
    (set-subalgebra? obj)
    (equal-universals? (included-elements obj) (underlying-set obj))))

(defn pointed-set?
  [obj]

  (and
    (set-subalgebra? obj)
    (= (count (included-elements obj)) 1)))

; Create a visualization of a subset by colorization
(defmethod visualize ::set-subalebra
  [coll]

  (output-graph!
    (dot/dot
     (dot/digraph
       [(dot/subgraph
          :cluster_0
          [{}
           (concat
             (map
               (fn [included-element]
                 [(.toString included-element)])
               (included-elements coll))
             (map
               (fn [excluded-element]
                 [(.toString excluded-element) {:style "filled", :fillcolor "lightgreen"}])
               (excluded-elements coll)))])]))))

