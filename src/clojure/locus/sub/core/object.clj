(ns locus.sub.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [dorothy.core :as dot]))

; Set subalgebras are subobjects in the topos Sets. They can equivalently be considered to be a
; special type of copresheaf of unary relations. We implement them with a special data type,
; overloaded images and inverse images on them, and use the logical connectives of Sets on them.
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

; Deconstructor function
(defn deconstruct-set-subalgebra
  [obj]

  [(included-elements obj) (underlying-set obj)])

; A constructor for set subalgebras
(defn set-subalgebra
  [a b]

  (SetSubalgebra. a b))

; Empty and full set subalgebras
(defn make-complete-set-subalgebra
  [coll]

  (SetSubalgebra. coll coll))

(defn make-empty-set-subalgebra
  [coll]

  (SetSubalgebra. #{} coll))

; Get subobject for a presheaf of unary relations
(defmulti get-subobject type)

(defmethod get-subobject ::set-subalebra
  [coll]

  (included-elements coll))

; Conversion routines for set subalgebras
(defmulti to-set-subalgebra type)

(defmethod to-set-subalgebra SetSubalgebra
  [^SetSubalgebra subalgebra] subalgebra)

(defmethod to-set-subalgebra :locus.set.logic.core.set/universal
  [coll]

  (SetSubalgebra. coll coll))

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

; Logical operators on set subalgebras
(defn complement-set-subalgebra
  [coll]

  (->SetSubalgebra
    (difference (underlying-set coll) (included-elements coll))
    (underlying-set coll)))

; Logical constructors for set subalgebras
(defn empty-set-subalgebra
  [coll]

  (make-empty-set-subalgebra (underlying-set coll)))

(defn complete-set-subalgebra
  [coll]

  (make-complete-set-subalgebra (underlying-set coll)))

; Join and meet of subobjects of sets
(defn join-set-subalgebras
  [& set-subalgebras]

  (SetSubalgebra.
    (apply union (map included-elements set-subalgebras))
    (apply union (map underlying-set set-subalgebras))))

(defn meet-set-subalgebras
  [& set-subalgebras]

  (SetSubalgebra.
    (apply intersection (map included-elements set-subalgebras))
    (apply intersection (map underlying-set set-subalgebras))))

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

(defn complete-set-subalgebra?
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
                  [(.toString included-element) {:style "filled", :fillcolor "lightgreen"}])
                (included-elements coll))
              (map
                (fn [excluded-element]
                  [(.toString excluded-element)])
                (excluded-elements coll)))])]))))