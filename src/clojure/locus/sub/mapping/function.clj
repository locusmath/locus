(ns locus.sub.mapping.function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.function.inclusion.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.square.core.morphism :refer :all]
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

(derive ::set-subfunction :locus.set.logic.structure.protocols/structured-function)
(derive SetSubfunction ::set-subfunction)

; The five main set parts of a subobject in the Sierpinski topos
(defn included-inputs
  [func]

  (included-elements (source-object func)))

(defn absent-inputs
  [func]

  (let [possible-outputs (set (included-elements (target-object func)))]
    (set
      (filter
        (fn [i]
          (contains? possible-outputs (func i)))
        (excluded-elements (source-object func))))))

(defn negative-inputs
  [func]

  (let [possible-outputs (set (included-elements (target-object func)))]
    (set
      (filter
        (fn [i]
          (not (contains? possible-outputs (func i))))
        (underlying-set (source-object func))))))

(defn included-outputs
  [func]

  (included-elements (target-object func)))

(defn excluded-outputs
  [func]

  (excluded-elements (target-object func)))

; Additional components of set subfunctions
(defn excluded-inputs
  [func]

  (excluded-elements (source-object func)))

(defn included-transition
  [func]

  (list (included-inputs func) (included-outputs func)))

; Helper utility functions to handle the input and output components of subfunctions
(defn modify-subfunction-components
  [set-subfunction new-in new-out]

  (->SetSubfunction
    (set-subalgebra new-in (inputs set-subfunction))
    (set-subalgebra new-out (outputs set-subfunction))
    (underlying-function set-subfunction)))

(defn modify-subfunction-input
  [set-subfunction new-in]

  (->SetSubfunction
    (set-subalgebra new-in (inputs set-subfunction))
    (target-object set-subfunction)
    (underlying-function set-subfunction)))

(defn modify-subfunction-output
  [set-subfunction new-out]

  (->SetSubfunction
    (source-object set-subfunction)
    (set-subalgebra new-out (outputs set-subfunction))
    (underlying-function set-subfunction)))

; The Sierpinski topos has fifteen logical operators on its object of truth values.
(defn empty-source
  [set-subfunction]

  (modify-subfunction-input set-subfunction #{}))

(defn hole
  [set-subfunction]

  (modify-subfunction-input set-subfunction (absent-inputs set-subfunction)))

(defn fill
  [set-subfunction]

  (modify-subfunction-input
    set-subfunction
    (union (included-inputs set-subfunction) (absent-inputs set-subfunction))))

(defn empty-subfunction
  [set-subfunction]

  (modify-subfunction-components set-subfunction #{} #{}))

(defn subfunction-negation
  [set-subfunction]

  (modify-subfunction-components
    set-subfunction
    (negative-inputs set-subfunction)
    (excluded-outputs set-subfunction)))

(defn empty-source-subfunction-negation
  [set-subfunction]

  (modify-subfunction-components set-subfunction #{} (excluded-outputs set-subfunction)))

(defn comiddle
  [set-subfunction]

  (modify-subfunction-components
    set-subfunction
    (union (negative-inputs set-subfunction) (included-inputs set-subfunction))
    (outputs set-subfunction)))

(defn cosource
  [set-subfunction]

  (modify-subfunction-components
    set-subfunction
    (union (negative-inputs set-subfunction) (absent-inputs set-subfunction))
    (outputs set-subfunction)))

(defn complete-subfunction
  [set-subfunction]

  (modify-subfunction-components set-subfunction (inputs set-subfunction) (outputs set-subfunction)))

(defn empty-source-cocompletion
  [set-subfunction]

  (modify-subfunction-components set-subfunction #{} (outputs set-subfunction)))

(defn negation-cocompletion
  [set-subfunction]

  (modify-subfunction-components set-subfunction (negative-inputs set-subfunction) (outputs set-subfunction)))

(defn hole-cocompletion
  [set-subfunction]

  (modify-subfunction-components set-subfunction (absent-inputs set-subfunction) (outputs set-subfunction)))

(defn fill-cocompletion
  [set-subfunction]

  (modify-subfunction-components
    set-subfunction
    (union (included-inputs set-subfunction) (absent-inputs set-subfunction))
    (outputs set-subfunction)))

(defn cocompletion
  [set-subfunction]

  (modify-subfunction-components set-subfunction (included-inputs set-subfunction) (outputs set-subfunction)))

; Logical connectives in the Sierpinski topos
(defn join-subfunctions
  [& set-subfunctions]

  (->SetSubfunction
    (apply join-set-subalgebras (map source-object set-subfunctions))
    (apply join-set-subalgebras (map target-object set-subfunctions))
    (first set-subfunctions)))

(defn meet-subfunctions
  [& set-subfunctions]

  (->SetSubfunction
    (apply meet-set-subalgebras (map source-object set-subfunctions))
    (apply meet-set-subalgebras (map target-object set-subfunctions))
    (first set-subfunctions)))

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
(defmethod visualize ::set-subfunction
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

; some truth theoretic arrows
(def T
  (SetSubfunction.
    (->SetSubalgebra '#{1} '#{0 1})
    (->SetSubalgebra #{"1F" "1T"} #{"0F" "0T" "1F" "1T"})
    {0 "0T" 1 "1T"}))

(def F
  (SetSubfunction.
    (->SetSubalgebra '#{1} '#{0 1})
    (->SetSubalgebra #{"1F" "1T"} #{"0F" "0T" "1F" "1T"})
    {0 "0F" 1 "1F"}))

(def omega
  (->SetSubalgebra #{"1F" "1T"} #{"0F" "0T" "1F" "1T"}))

(def omega-squared
  (->SetSubalgebra
    #{"1FF" "1FT" "1TF" "1TT"}
    #{"0FF" "0FT" "0TF" "0TT"
      "1FF" "1FT" "1TF" "1TT"}))

(def AND
  (SetSubfunction.
    omega-squared
    omega
    {"0FF" "0F"
     "0TF" "0F"
     "0FT" "0F"
     "0TT" "0T"
     "1FF" "1F"
     "1TF" "1F"
     "1FT" "1F"
     "1TT" "1T"}))

(def OR
  (SetSubfunction.
    omega-squared
    omega
    {"0FF" "0F"
     "0TF" "0T"
     "0FT" "0T"
     "0TT" "0T"
     "1FF" "1F"
     "1TF" "1T"
     "1FT" "1T"
     "1TT" "1T"}))

(def IMPL
  (SetSubfunction.
    omega-squared
    omega
    {"0FF" "0T"
     "0TF" "0F"
     "0FT" "0T"
     "0TT" "0T"
     "1FF" "1T"
     "1TF" "1F"
     "1FT" "1T"
     "1TT" "1T"}))




