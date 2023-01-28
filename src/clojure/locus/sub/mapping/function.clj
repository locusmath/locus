(ns locus.sub.mapping.function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.function.inclusion.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all]
            [dorothy.core :as dot])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; A subfunction of a function f: A -> B is a homomorphism of unary relations, or subsets in A
; and B. So in other words, for subsets like S of A and T of B then this means that the f(S)
; image is contained in B. These are then morphisms in a category of unary relations, and
; subalgebras can be composed accordingly.
(deftype SetSubfunction [source target func]
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

(derive SetSubfunction :locus.set.logic.structure.protocols/structured-function)

; Included inputs and outputs
(defn included-inputs
  [func]

  (included-elements (source-object func)))

(defn excluded-inputs
  [func]

  (excluded-elements (source-object func)))

(defn included-outputs
  [func]

  (included-elements (target-object func)))

(defn excluded-outputs
  [func]

  (excluded-elements (target-object func)))

(defn included-transition
  [func]

  (list (included-inputs func) (included-outputs func)))

; A constuctor for set subfunctions
(defn set-subfunction
  [func a b]

  (->SetSubfunction
    (set-subalgebra a (inputs func))
    (set-subalgebra b (outputs func))
    func))

; Every function is naturally associated to a surjective interior
(defn surjective-set-subfunction
  [func]

  (->SetSubfunction
    (make-complete-set-subalgebra (inputs func))
    (set-subalgebra (function-image func) (outputs func))
    func))

; Given a subfunction f: A -> B defined by (S,T) the surjective component of (S,T) is created by the
; intersection of T with the function image of f.
(defn set-subfunction-surjective-interior
  [set-subfunction]

  (let [func (underlying-function set-subfunction)]
    (->SetSubfunction
     (source-object set-subfunction)
     (set-subalgebra
       (intersection (included-outputs set-subfunction) (function-image func))
       (outputs set-subfunction))
     func)))

; Get the function induced by a set subfunction
(defmethod get-subobject SetSubfunction
  [set-subfunction]

  (let [func (underlying-function set-subfunction)]
    (subfunction func (included-inputs set-subfunction) (included-outputs set-subfunction))))

; Conversion routines
(defmulti to-set-subfunction type)

(defmethod to-set-subfunction SetSubfunction
  [func] func)

(defmethod to-set-subfunction SetFunction
  [func]

  (->SetSubfunction
    (make-complete-set-subalgebra (inputs func))
    (make-complete-set-subalgebra (outputs func))
    func))

; Subalgebras have all products and coproducts
(defmethod coproduct SetSubfunction
  [& functions]

  (->SetSubfunction
    (apply coproduct (map source-object functions))
    (apply coproduct (map target-object functions))
    (fn [[i v]]
      (list i ((nth functions i) v)))))

(defmethod product SetSubfunction
  [& functions]

  (->SetSubfunction
    (apply product (map source-object functions))
    (apply product (map target-object functions))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth functions i) v))
        coll))))

; Ontology of set subfunctions
(defn set-subfunction?
  [obj]

  (= (type obj) SetSubfunction))

; Visualise subfunctions as graphviz diagrams
(defmethod visualize SetSubfunction
  [func]

  (let [in-seq (vec (seq (inputs func)))
        out-seq (vec (seq (outputs func)))
        in-count (count in-seq)
        highlighting-style {:style     "filled"
                            :fillcolor "lightgreen"}
        create-node (fn [highlighted? node-name node-label]
                      [(.toString node-name)
                       (merge
                         {:label (.toString node-label)}
                         (if highlighted?
                           highlighting-style
                           {}))])
        in-cluster [(dot/subgraph
                      :cluster_0
                      [{}
                       (map-indexed
                         (fn [i in-element]
                           (create-node
                             (contains? (included-inputs func) in-element)
                             i
                             in-element))
                         in-seq)])]
        out-cluster [(dot/subgraph
                       :cluster_1
                       [{}
                        (map-indexed
                          (fn [i out-element]
                            (create-node
                              (contains? (included-outputs func) out-element)
                              (+ i in-count)
                              out-element))
                          out-seq)])]]
    (output-graph!
      (dot/dot
       (dot/digraph
         [{:rankdir "LR"}
          in-cluster
          out-cluster
          (map-indexed
            (fn [i in-element]
              [(.toString i) (.toString (+ in-count (.indexOf out-seq (func in-element))))])
            in-seq)])))))