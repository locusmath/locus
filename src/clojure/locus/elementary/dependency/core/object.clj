(ns locus.elementary.dependency.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.order.core.object :refer :all]
            [locus.elementary.triangle.core.object :refer :all]
            [locus.elementary.incidence.core.object :refer :all]
            [locus.elementary.cospan.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.difunction.dibijection.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.bijection.core.morphism :refer :all]
            [locus.elementary.dependency.nset.object :refer :all]
            [locus.elementary.dependency.nfunction.object :refer :all]
            [locus.elementary.dependency.nbijection.object :refer :all]
            [locus.elementary.dependency.chain.object :refer :all]
            [locus.elementary.triangle.core.morphism :refer :all]
            [locus.elementary.incidence.core.morphism :refer :all]
            [locus.elementary.cospan.core.morphism :refer :all]
            [locus.elementary.diamond.core.morphism :refer :all]
            [locus.elementary.dependency.chain.morphism :refer :all])
  (:import (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.triangle.core.object SetTriangle)
           (locus.elementary.incidence.core.object Span)
           (locus.elementary.cospan.core.object Cospan)
           (locus.elementary.difunction.core.object Difunction)
           (locus.elementary.difunction.dibijection.object Dibijection)
           (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.bijection.core.morphism Gem)
           (locus.elementary.dependency.nset.object NSet)
           (locus.elementary.dependency.nfunction.object NFunction)
           (locus.elementary.dependency.nbijection.object NBijection)
           (locus.elementary.dependency.chain.object SetChain)
           (locus.elementary.triangle.core.morphism TriangleMorphism)
           (locus.elementary.incidence.core.morphism MorphismOfSpans)
           (locus.elementary.cospan.core.morphism MorphismOfCospans)
           (locus.elementary.diamond.core.morphism Cube)
           (locus.elementary.dependency.chain.morphism ChainMorphism)
           (locus.base.function.core.object SetFunction)))

; Copresheaves over preorders Sets^P
; These are generalisations of functional dependencies of relations.
(deftype Dependency [order object-function morphism-function]
  StructuredDifunction
  (first-function [this]
    morphism-function)
  (second-function [this]
    object-function))

; Get the sets and functions associated with dependency copresheaves
(defmethod get-set Dependency
  [^Dependency dependency, x]

  (object-apply dependency x))

(defmethod get-function Dependency
  [^Dependency dependency, x]

  (morphism-apply dependency x))

; Index preorders for copresheaves over preorders
(defmethod index :default
  [obj] nil)

(defmethod index :locus.base.logic.core.set/universal
  [coll]

  (relational-preposet
    (weak-order [#{0}])))

(defmethod index :locus.base.logic.structure.protocols/set-function
  [func]

  (relational-poset
    (weak-order [#{0} #{1}])))

(defmethod index :locus.elementary.copresheaf.core.protocols/diset
  [diset]

  (relational-preposet
    (weak-order [#{0 1}])))

(defmethod index :locus.elementary.copresheaf.core.protocols/bijection
  [bijection]

  (relational-preposet
    (total-preorder [#{0 1}])))

(defmethod index SetTriangle
  [triangle]

  (relational-poset
    (total-order 0 1 2)))

(defmethod index Span
  [span]

  (relational-poset
    (weak-order [#{0} #{1 2}])))

(defmethod index Cospan
  [cospan]

  (relational-poset
    (weak-order [#{0 1} #{2}])))

(defmethod index Difunction
  [difunction]

  (product
    (to-poset (total-order 0 1))
    (to-poset (weak-order [#{0 1}]))))

(defmethod index Dibijection
  [dibijection]

  (product
    (to-preposet (total-preorder [#{0 1}]))
    (to-preposet (weak-order [#{0 1}]))))

(defmethod index Diamond
  [diamond]

  (product
    (to-poset (total-order 0 1))
    (to-poset (total-order 0 1))))

(defmethod index Gem
  [gem]

  (product
    (to-poset (total-order 0 1))
    (to-preposet (total-preorder [#{0 1}]))))

(defmethod index MorphismOfCospans
  [morphism]

  (product
    (to-poset (total-order 0 1))
    (to-poset (weak-order [#{0 1} #{2}]))))

(defmethod index Cube
  [cube]

  (product
    (to-poset (total-order 0 1))
    (product
      (to-poset (total-order 0 1))
      (to-poset (total-order 0 1)))))

(defmethod index MorphismOfSpans
  [morphism]

  (product
    (to-poset (total-order 0 1))
    (to-poset (weak-order [#{0} #{1 2}]))))

(defmethod index TriangleMorphism
  [morphism]

  (product
    (to-poset (total-order 0 1))
    (to-poset (total-order 0 1 2))))

(defmethod index NSet
  [nset]

  (nth-antichain (nset-type nset)))

(defmethod index NFunction
  [nfunction]

  (product
    (to-poset (total-order 0 1))
    (nth-antichain (nfunction-type nfunction))))

(defmethod index NBijection
  [nbijection]

  (product
    (to-preposet (total-preorder [#{0 1}]))
    (nth-antichain (nbijection-type nbijection))))

(defmethod index SetChain
  [^SetChain chain]

  (nth-chain (inc (count (composition-sequence chain)))))

(defmethod index ChainMorphism
  [morphism]

  (product
    (to-poset (total-order 0 1))
    (index (source-object morphism))))

(defmethod index Dependency
  [^Dependency dependency] (.-order dependency))

; Convert presheaves over preorders into a common format
(defmulti to-dependency type)

(defmethod to-dependency Dependency
  [dependency] dependency)

(defmethod to-dependency :default
  [dependency]

  (let [dep (index dependency)]
    (if (nil? dep)
      (throw (new IllegalArgumentException))
      (->Dependency dep (partial get-set dependency) (partial get-function dependency)))))

; The topos of lower bijective triangles consists of presheaves over the total
; preorder [2,1]. Its elements are like special cases of triangle copresheaves over
; the total order [1,1,1] except their lower half is invertible.
(def two-one-preorder
  (relational-preposet (total-preorder [#{0 1} #{2}])))

(defn lower-bijective-triangle
  [func bijection]

  (let [s0 (inputs bijection)
        s1 (outputs bijection)
        s2 (outputs func)]
    (->Dependency
      two-one-preorder
      (fn [obj]
        (case obj
          0 s0
          1 s1
          2 s2))
      (fn [a b]
        (case [a b]
          [0 0] (identity-function s0)
          [1 1] (identity-function s1)
          [2 2] (identity-function s2)
          [0 1] (underlying-function bijection)
          [1 0] (underlying-function (inv bijection))
          [0 2] (compose func (underlying-function bijection))
          [1 2] func)))))

(defn relational-lower-bijective-triangle
  [rel]

  (lower-bijective-triangle
    (relation-transition-map rel 1 2)
    (make-bijection-by-function-pair
      (relation-transition-map rel 0 1)
      (relation-transition-map rel 1 0))))

; The topos of upper bijective triangles consists of presheaves over the total
; preorder [1,2]. Its elements are like triangle copresheaves over the total order
; [1,1,1] except their upper half is invertible.
(def one-two-preorder
  (relational-preposet (total-preorder [#{0} #{1 2}])))

(defn upper-bijective-triangle
  [bijection func]

  (let [s0 (inputs func)
        s1 (outputs func)
        s2 (outputs bijection)]
    (->Dependency
      two-one-preorder
      (fn [obj]
        (case obj
          0 s0
          1 s1
          2 s2))
      (fn [[a b]]
        (case [a b]
          [0 0] (identity-function s0)
          [1 1] (identity-function s1)
          [2 2] (identity-function s2)
          [1 2] (underlying-function bijection)
          [2 1] (underlying-function (inv bijection))
          [0 1] func
          [0 2] (compose (underlying-function bijection) func))))))

(defn relational-upper-bijective-triangle
  [rel]

  (upper-bijective-triangle
    (make-bijection-by-function-pair
      (relation-transition-map rel 1 2)
      (relation-transition-map rel 2 1))
    (relation-transition-map rel 0 1)))

; The topos of trijections is a natural generalisation of the topos of bijections to
; a morphism on three objects. Like the topos of bijections, it is boolean and all of
; its algebraic properties coincide with the topos of sets.
(def k3-preorder
  (relational-preposet
    (total-preorder [#{0 1 2}])))

(defn trijection
  [f g]

  (let [s0 (inputs g)
        s1 (outputs g)
        s2 (outputs f)]
    (->Dependency
      k3-preorder
      (fn [obj]
        (case obj
          0 s0
          1 s1
          2 s2))
      (fn [[a b]]
        (case [a b]
          [0 0] (identity-function s0)
          [0 1] (underlying-function g)
          [0 2] (underlying-function (compose f g))
          [1 0] (underlying-function (inv g))
          [1 1] (identity-function s1)
          [1 2] (underlying-function f)
          [2 0] (underlying-function (inv (compose f g)))
          [2 1] (underlying-function (inv f))
          [2 2] (identity-function s2))))))

(defn relational-trijection
  [rel]

  (trijection
    (make-bijection-by-function-pair
      (relation-transition-map rel 1 2)
      (relation-transition-map rel 2 1))
    (make-bijection-by-function-pair
      (relation-transition-map rel 0 1)
      (relation-transition-map rel 1 0))))

; The topos of set function pairs is the topos of copresheaves over the index category
; T_2 + 1. So it is another example of a presheaf topos of a preorder.
(def t2-plus-one-order
  (relational-poset '#{(0 0) (1 1) (2 2) (1 2)}))

(defn set-function-pair
  [coll func]

  (let [s0 coll
        s1 (inputs func)
        s2 (outputs func)]
    (Dependency.
      t2-plus-one-order
      (fn [obj]
        (case obj
          0 s0
          1 s1
          2 s2))
      (fn [[a b]]
        (case [a b]
          [0 0] (identity-function s0)
          [1 1] (identity-function s1)
          [2 2] (identity-function s2)
          [1 2] func)))))

; The topos of set and bijection pairs is the topos of copresheaves over the index category
; K_2 + 1. So it is another example of a presheaf topos of a preorder.
(def k2-plus-one-preorder
  (relational-preposet '#{(0 0) (1 1) (2 2) (1 2) (2 1)}))

(defn set-bijection-pair
  [coll bijection]

  (let [s0 coll
        s1 (inputs bijection)
        s2 (outputs bijection)]
    (Dependency.
      k2-plus-one-preorder
      (fn [obj]
        (case obj
          0 s0
          1 s1
          2 s2))
      (fn [[a b]]
        (case [a b]
          [0 0] (identity-function s0)
          [1 1] (identity-function s1)
          [2 2] (identity-function s2)
          [1 2] (underlying-function bijection)
          [2 1] (underlying-function (inv bijection)))))))

; The topos of triples of sets Sets^3 is the next level generalisation of the topos of pairs
; of sets Sets^2 to three objects instead of two. It is again a boolean topos, as it
; shares that property with the topos Sets^2 but unlike Sets it is not bivalent.
(def e3-order
  (relational-poset (coreflexive-relation #{0 1 2})))

(defn triset
  [a b c]

  (->Dependency
    e3-order
    (fn [n]
      (case n
        0 a
        1 b
        2 c))
    (fn [[i j]]
      (case [i j]
        [0 0] (identity-function a)
        [1 1] (identity-function b)
        [2 2] (identity-function c)))))

; Copresheaves for generalized incidence structures
(defn nth-span-order
  [n]

  (relational-poset
    (weak-order
      [#{0} (set (range 1 (inc n)))])))

(defn nspan
  [& funcs]

  (let [n (count funcs)]
    (letfn [(nth-set [i]
              (if (zero? i)
                (inputs (first funcs))
                (outputs (nth funcs (dec i)))))]
      (Dependency.
        (nth-span-order n)
        nth-set
        (fn [[i j]]
          (if (= i j)
            (identity-function (nth-set i))
            (nth funcs (dec j))))))))

; Copresheaves for generalized cospans
(defn nth-cospan-order
  [n]

  (relational-poset
    (weak-order
      [(set (range 1 (inc n))) #{0}])))

(defn ncospan
  [& funcs]

  (let [n (count funcs)]
    (letfn [(nth-set [i]
              (if (zero? i)
                (outputs (first funcs))
                (inputs (nth funcs (dec i)))))]
      (Dependency.
        (nth-cospan-order n)
        nth-set
        (fn [[i j]]
          (if (= i j)
            (identity-function (nth-set i))
            (nth funcs (dec i))))))))

; Multi incidence relations defined by indexed membership relations.
(defn multi-incidence-order
  [n]

  (relational-poset
    (weak-order
      [(set (range n))
       (set (range n (+ n 2)))])))

(def two-two-order
  (multi-incidence-order 2))

(defn nth-member-flags
  [vertices edges n]

  (seqable-binary-relation
    edges
    vertices
    (fn [[edge vertex]]
      (contains? (nth edge n) vertex))))

(defn multi-incidence-structure
  ([vertices edges]
   (multi-incidence-structure vertices edges (count (first edges))))
  ([vertices edges arity]

   (let [edge-index (+ arity 1)
         vertex-index (+ arity 2)]
     (letfn [(get-component-set [n]
               (cond
                 (< n arity) (nth-member-flags vertices edges n)
                 (= n edge-index) edges
                 (= n vertex-index) vertices))
             (get-component-function [[i j]]
               (cond
                 (= i j) (identity-function (get-component-set i))
                 (= j edge-index) (->SetFunction
                                    (nth-member-flags vertices edges i)
                                    edges
                                    first)
                 (= j vertex-index) (->SetFunction
                                      (nth-member-flags vertices edges i)
                                      vertices
                                      second)))]
       (->Dependency
         (multi-incidence-order arity)
         get-component-set
         get-component-function)))))

(defn crown
  [vertices edges] (multi-incidence-structure vertices edges 2))

; Presheaves over the weak order [1,1,2]
(def lower-common-tree
  (relational-poset
    (weak-order [#{0} #{1} #{2 3}])))

(defn combine-prefunction-equal-triangles
  [triangle1 triangle2]

  (letfn [(get-component-set [n]
            (case n
              0 (triangle-source triangle1)
              1 (triangle-middle triangle1)
              2 (triangle-target triangle1)
              3 (triangle-target triangle2)))
          (get-component-function [[i j]]
            (if (= i j)
              (identity-function (get-component-set i))
              (case [i j]
                [0 1] (prefunction triangle1)
                [0 2] (compfunction triangle1)
                [0 3] (compfunction triangle2)
                [1 2] (postfunction triangle1)
                [1 3] (postfunction triangle2))))]
    (->Dependency
      lower-common-tree
      get-component-set
      get-component-function)))

; Presheaves over the weak order [2, 1, 1]
(def upper-common-tree
  (relational-poset
    (weak-order [#{0 1} #{2} #{3}])))

(defn combine-postfunction-equal-triangles
  [triangle1 triangle2]

  (letfn [(get-component-set [n]
            (case n
              0 (triangle-source triangle1)
              1 (triangle-source triangle2)
              2 (triangle-middle triangle1)
              3 (triangle-target triangle1)))
          (get-component-function [[i j]]
            (if (= i j)
              (identity-function (get-component-set i))
              (case [i j]
                [0 2] (prefunction triangle1)
                [0 3] (compfunction triangle1)
                [1 2] (prefunction triangle2)
                [1 3] (compfunction triangle2)
                [2 3] (postfunction triangle1))))]
    (->Dependency
      upper-common-tree
      get-component-set
      get-component-function)))

; Presheaves over the disjoint union of total orders T_3 + T_3
(def ditriangle-order
  (relational-poset
    '#{(0 0) (1 1) (2 2) (0 1) (0 2) (1 2) (3 3) (4 4) (5 5) (3 5) (3 4) (4 5)}))

(defn ditriangle
  [triangle1 triangle2]

  (Dependency.
    ditriangle-order
    (fn [obj]
      (case obj
        0 (triangle-source triangle1)
        1 (triangle-middle triangle1)
        2 (triangle-target triangle1)
        3 (triangle-source triangle2)
        4 (triangle-middle triangle2)
        5 (triangle-target triangle2)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (triangle-source triangle1))
        [1 1] (identity-function (triangle-middle triangle1))
        [2 2] (identity-function (triangle-target triangle1))
        [3 3] (identity-function (triangle-source triangle2))
        [4 4] (identity-function (triangle-middle triangle2))
        [5 5] (identity-function (triangle-target triangle2))
        [0 1] (prefunction triangle1)
        [0 2] (compfunction triangle1)
        [1 2] (postfunction triangle1)
        [3 4] (prefunction triangle2)
        [3 5] (compfunction triangle2)
        [4 5] (postfunction triangle2)))))

(defn combine-composable-difunctions
  [f g]

  (ditriangle
    (SetTriangle. (first-function f) (first-function g))
    (SetTriangle. (second-function f) (second-function g))))

; Create a multijection copresheaf over a complete thin groupoid
(defn multijection
  [& args]

  (let [bijections (reverse args)
        n (count bijections)]
    (letfn [(nth-set [i]
              (if (zero? i)
                (inputs (first bijections))
                (outputs (nth bijections (dec i)))))
            (nth-function [[i j]]
              (cond
                (= i j) (identity-function (nth-set i))
                (< i j) (apply
                          compose
                          (map
                            (fn [k]
                              (underlying-function (nth bijections k)))
                            (range i j)))
                (< j i) (apply
                          compose
                          (map
                            (fn [k]
                              (underlying-function (inv (nth bijections k))))
                            (reverse (range j i))))))]
      (->Dependency
        (nth-complete-preorder (inc n))
        nth-set
        nth-function))))

; Generalized tuples of sets and functions
(defn height-two-multichain-order
  [n k]

  (union
    (weak-order [(set (range n))])
    (set
      (mapcat
       (fn [i]
         (let [start-index (+ n (* 2 i))]
           #{(list start-index start-index)
             (list start-index (inc start-index))
             (list (inc start-index) (inc start-index))}))
       (range k)))))

(defn set-and-function-system
  [sets functions]

  (letfn [(get-component-set [n]
            (if (< n (count sets))
              (nth sets n)
              (let [adjusted-index (- n (count sets))]
                (if (even? adjusted-index)
                  (inputs (nth functions (/ adjusted-index 2)))
                  (outputs (nth functions (/ (dec adjusted-index) 2)))))))
          (get-component-function [[i j]]
            (if (= i j)
              (identity-function (get-component-set i))
              (let [adjusted-index (/ (- i (count sets)) 2)]
                (nth functions adjusted-index))))]
    (->Dependency
      (height-two-multichain-order (count sets) (count functions))
      get-component-set
      get-component-function)))

; Create dependency by morphism
(defn create-dependency-by-morphism
  [^Dependency source, ^Dependency target, ^clojure.lang.IFn func]

  (->Dependency
    (product
      (relational-preposet '#{(0 0) (1 1) (0 1)})
      (.-order source))
    (fn [[i v]]
      (case i
        0 (object-apply source v)
        1 (object-apply target v)))
    (fn [[[a b] [c d]]]
      (let [first-arrow [a c]
            second-arrow [b d]]
        (case first-arrow
          [0 0] (morphism-apply source second-arrow)
          [1 1] (morphism-apply target second-arrow)
          [0 1] (compose (morphism-apply target second-arrow) (func b)))))))

; Create a dependency functor from a relational copresheaf
; The underlying preorder of the ordering relation provided must be a preorder
; on the range of the first n elements, which is used as the indices to the
; tuples of the relation.
(defn relational-functional-dependencies
  [order rel]

  (->Dependency
    order
    (fn [i]
      (set
        (map
          (fn [tuple]
            (nth tuple i))
          rel)))
    (fn [[i j]]
      (relation-transition-map rel i j))))

; We need some way of dealing with functional dependencies
; This is only rudimentary at this stage of support and so it
; is due for a major refactoring involving the core system.
; and our basic notion of querying.
(defn induced-map
  [rel source target]

  (let [rval (apply
               merge
               (map
                 (fn [i]
                   {(restrict-list i source) (restrict-list i target)})
                 rel))]
    (if (nil? rval)
      {}
      rval)))

(defn induced-fn
  [rel source target]

  (fn [source-elements]
    (first
      (for [i rel
            :when (= (restrict-list i source) source-elements)]
        (restrict-list i target)))))

(defn induced-function
  [rel source target]

  (SetFunction.
    (project-relation rel source)
    (project-relation rel target)
    (induced-fn rel source target)))

(defn setwise-relational-functional-dependencies
  [dep rel]

  (Dependency.
    dep
    (fn [nums]
      (project-relation rel nums))
    (fn [[source target]]
      (induced-function rel source target))))

; Every single preorder P is naturally associated to a trivial copresheaf in Sets^P
; which takes each object and associates it to a singleton set, and then each
; map of singletons is the unique trivial function between them.
(defn trivial-dependency
  [preorder]

  (Dependency.
    preorder
    (fn [obj]
      #{obj})
    (fn [[a b]]
      (pair-function a b))))

; The copresheaf that takes a family of sets and that maps each ordered pair in its
; partial order expressed as a thin category to an inclusion function.
(defn inclusion-dependency
  [family]

  (Dependency.
    (->Poset
      family
      (family-inclusion-ordering family))
    identity
    (fn [[a b]]
      (inclusion-function a b))))

; Get the information necessary to turn a dependency copresheaf into a visualisation
(defn object-indexed-family
  [copresheaf]

  (let [cat (.-order copresheaf)]
    (into
      {}
      (map
        (fn [object]
          [object (object-apply copresheaf object)])
        (objects cat)))))

(defn generating-concrete-morphism-triples
  [copresheaf]

  (let [cat (.-order copresheaf)]
    (map
      (fn [[a b]]
        (list a b (morphism-apply copresheaf [a b])))
      (covering-relation (underlying-relation cat)))))

; Visualisation of dependency copresheaves
(defmethod visualize Dependency
  [^Dependency dependency]

  (let [[p v] (generate-copresheaf-data
                (object-indexed-family dependency)
                (generating-concrete-morphism-triples dependency))]
    (visualize-clustered-digraph* "BT" p v)))
