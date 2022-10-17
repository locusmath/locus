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
            [locus.elementary.dependency.nfunction.nbijection :refer :all]
            [locus.elementary.dependency.chain.object :refer :all]
            [locus.elementary.triangle.core.morphism :refer :all]
            [locus.elementary.incidence.core.morphism :refer :all]
            [locus.elementary.cospan.core.morphism :refer :all]
            [locus.elementary.diamond.core.morphism :refer :all]
            [locus.elementary.dependency.chain.morphism :refer :all])
  (:import (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.triangle.core.object TriangleCopresheaf)
           (locus.elementary.incidence.core.object Span)
           (locus.elementary.cospan.core.object Cospan)
           (locus.elementary.difunction.core.object Difunction)
           (locus.elementary.difunction.dibijection.object Dibijection)
           (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.bijection.core.morphism Gem)
           (locus.elementary.dependency.nset.object NSet)
           (locus.elementary.dependency.nfunction.object NFunction)
           (locus.elementary.dependency.nfunction.nbijection NBijection)
           (locus.elementary.dependency.chain.object ChainCopresheaf)
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

; Special types of preorders for use in defining dependency functors as copresheaves
(def trivial-order
  (relational-poset '#{(0 0)}))

(def t2-order
  (relational-poset '#{(0 0) (0 1) (1 1)}))

(def e2-order
  (relational-poset (coreflexive-relation #{0 1})))

(def k2-preorder
  (relational-preposet (complete-relation #{0 1})))

; Size three
(def t3-order
  (relational-poset (total-order 0 1 2)))

(def span-object-order
  (relational-poset (weak-order [#{0} #{1 2}])))

(def cospan-object-order
  (relational-poset (weak-order [#{0 1} #{2}])))

; Size four
(def difunction-order
  (relational-poset '#{(0 0) (1 1) (0 1) (2 2) (3 3) (2 3)}))

(def dibijection-preorder
  (relational-poset (equivalence-relation #{#{0 1} #{2 3}})))

(def diamond-order
  (relational-poset (weak-order [#{0} #{1 2} #{3}])))

(def gem-preorder
  (relational-preposet (total-preorder [#{0 1} #{2 3}])))

; Additional preorders
(def e3-order
  (relational-poset (coreflexive-relation #{0 1 2})))

(def k3-preorder
  (relational-preposet (complete-relation #{0 1 2})))

(def one-two-preorder
  (relational-preposet (total-preorder [#{0} #{1 2}])))

(def two-one-preorder
  (relational-preposet (total-preorder [#{0 1} #{2}])))

(def two-two-order
  (relational-poset (weak-order [#{0 1} #{2 3}])))

; Non connected preorders
(def t2-plus-one-order
  (relational-poset '#{(0 0) (1 1) (2 2) (1 2)}))

(def k2-plus-one-preorder
  (relational-preposet '#{(0 0) (1 1) (2 2) (1 2) (2 1)}))

(def ditriangle-order
  (relational-poset
    '#{(0 0) (1 1) (2 2) (0 1) (0 2) (1 2) (3 3) (4 4) (5 5) (3 5) (3 4) (4 5)}))

; Mechanisms for converting copresheaves into dependency functors
; These mechanisms convert the various familiar copresheaves over preorders like sets, functions,
; bijections, morphisms of functions, morphisms of bijections, disets, morphisms of disets,
; morphisms of diamonds, spans, cospans, and so on into members of the dependency functor
; class. The class of dependency functors, which defines all copresheaves over preorders
; is now a common mechanism for studying the different types of copresheaves over preorders.
(defmulti to-dependency type)

(defmethod to-dependency :locus.base.logic.core.set/universal
  [coll]

  (->Dependency
    trivial-order
    (fn [obj]
      coll)
    (fn [[a b]]
      (identity-function coll))))

(defmethod to-dependency :locus.base.logic.structure.protocols/set-function
  [func]

  (->Dependency
    t2-order
    (fn [obj]
      (case obj
        0 (inputs func)
        1 (outputs func)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (inputs func))
        [1 1] (identity-function (outputs func))
        [0 1] func))))

(defmethod to-dependency :locus.elementary.copresheaf.core.protocols/diset
  [diset]

  (->Dependency
    e2-order
    (fn [obj]
      (case obj
        0 (first-set diset)
        1 (second-set diset)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (first-set diset))
        [1 1] (identity-function (second-set diset))))))

(defmethod to-dependency :locus.elementary.copresheaf.core.protocols/bijection
  [^Bijection bijection]

  (->Dependency
    k2-preorder
    (fn [obj]
      (case obj
        0 (inputs bijection)
        1 (outputs bijection)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (inputs bijection))
        [1 1] (identity-function (outputs bijection))
        [0 1] (underlying-function bijection)
        [1 0] (underlying-function (inv bijection))))))

(defmethod to-dependency Span
  [^Span span]

  (->Dependency
    span-object-order
    (fn [obj]
      (case obj
        0 (span-flags span)
        1 (span-edges span)
        2 (span-vertices span)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (span-flags span))
        [1 1] (identity-function (span-edges span))
        [2 2] (identity-function (span-vertices span))
        [0 1] (edge-function span)
        [0 2] (vertex-function span)))))

(defmethod to-dependency Cospan
  [^Cospan cospan]

  (->Dependency
    cospan-object-order
    (fn [obj]
      (case obj
        0 (first-cospan-source cospan)
        1 (second-cospan-source cospan)
        2 (cospan-target cospan)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (first-cospan-source cospan))
        [1 1] (identity-function (second-cospan-source cospan))
        [2 2] (identity-function (cospan-target cospan))
        [0 2] (first-cospan-function cospan)
        [1 2] (second-cospan-function cospan)))))

(defmethod to-dependency TriangleCopresheaf
  [^TriangleCopresheaf triangle]

  (->Dependency
    t3-order
    (fn [obj]
      (case obj
        0 (triangle-source triangle)
        1 (triangle-middle triangle)
        2 (triangle-target triangle)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (triangle-source triangle))
        [1 1] (identity-function (triangle-middle triangle))
        [2 2] (identity-function (triangle-target triangle))
        [0 1] (prefunction triangle)
        [1 2] (postfunction triangle)
        [0 2] (compfunction triangle)))))

(defmethod to-dependency Difunction
  [^Difunction difunction]

  (->Dependency
    difunction-order
    (fn [obj]
      (case obj
        0 (inputs (first-function difunction))
        1 (outputs (first-function difunction))
        2 (inputs (second-function difunction))
        3 (outputs (second-function difunction))))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (inputs (first-function difunction)))
        [1 1] (identity-function (outputs (first-function difunction)))
        [2 2] (identity-function (inputs (second-function difunction)))
        [3 3] (identity-function (outputs (second-function difunction)))
        [0 1] (first-function difunction)
        [2 3] (second-function difunction)))))

(defmethod to-dependency Dibijection
  [^Dibijection dibijection]

  (->Dependency
    dibijection-preorder
    (fn [obj]
      (case obj
        0 (inputs (first-function dibijection))
        1 (outputs (first-function dibijection))
        2 (inputs (second-function dibijection))
        3 (outputs (second-function dibijection))))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (inputs (first-function dibijection)))
        [1 1] (identity-function (outputs (first-function dibijection)))
        [2 2] (identity-function (inputs (second-function dibijection)))
        [3 3] (identity-function (outputs (second-function dibijection)))
        [0 1] (first-function dibijection)
        [1 0] (underlying-function (inv (first-bijection dibijection)))
        [2 3] (second-function dibijection)
        [3 2] (underlying-function (inv (second-bijection dibijection)))))))

(defmethod to-dependency Diamond
  [^Diamond diamond]

  (->Dependency
    diamond-order
    (fn [obj]
      (case obj
        0 (source-input-set diamond)
        1 (source-output-set diamond)
        2 (target-input-set diamond)
        3 (target-output-set diamond)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-function (source-input-set diamond))
        [1 1] (identity-function (source-output-set diamond))
        [2 2] (identity-function (target-input-set diamond))
        [3 3] (identity-function (target-output-set diamond))

        [0 1] (source-object diamond)
        [2 3] (target-object diamond)

        [0 2] (first-function diamond)
        [1 3] (second-function diamond)

        [0 3] (common-composite-set-function diamond)))))

(defmethod to-dependency Gem
  [^Gem gem]

  (let [source-bijection (source-object gem)
        target-bijection (target-object gem)]
    (->Dependency
     gem-preorder
     (fn [obj]
       0 (inputs (source-object gem))
       1 (outputs (source-object gem))
       2 (inputs (target-object gem))
       3 (outputs (target-object gem)))
     (fn [[a b]]
       (case [a b]
         [0 0] (identity-function (inputs (source-object gem)))
         [1 1] (identity-function (outputs (source-object gem)))
         [2 2] (identity-function (inputs (target-object gem)))
         [3 3] (identity-function (outputs (target-object gem)))
         [0 1] (underlying-function source-bijection)
         [1 0] (underlying-function (inv source-bijection))
         [2 3] (underlying-function target-bijection)
         [3 2] (underlying-function (inv target-bijection))
         [0 2] (first-function gem)
         [0 3] (compose (underlying-function target-bijection) (first-function gem))
         [1 2] (compose (underlying-function (inv target-bijection)) (second-function gem))
         [1 3] (second-function gem))))))

; Conversion routines for generally sized copresheaves
(defmethod to-dependency NSet
  [^NSet nset]

  (let [colls (.-colls nset)
        n (count colls)]
    (->Dependency
      (nth-antichain n)
      (fn [i]
        (nth-set nset i))
      (fn [[i j]]
        (identity-function (nth-set nset i))))))

(defmethod to-dependency NFunction
  [^NFunction nfunction]

  (let [funcs (.-funcs nfunction)
        arity (count funcs)]
    (letfn [(nth-set [obj]
              (if (even? obj)
                (inputs (nth funcs (/ obj 2)))
                (outputs (nth funcs (/ (dec obj) 2)))))
            (get-function [[n m]]
              (if (= n m)
                (identity-function (nth-set n))
                (nth funcs (int (/ n 2)))))]
      (->Dependency (n-pair-order arity) nth-set get-function))))

(defmethod to-dependency NBijection
  [^NBijection nbijection]

  (let [funcs (.-bijections nbijection)
        arity (count funcs)]
    (letfn [(nth-set [obj]
              (if (even? obj)
                (inputs (nth funcs (/ obj 2)))
                (outputs (nth funcs (/ (dec obj) 2)))))
            (get-function [[n m]]
              (if (= n m)
                (identity-function (nth-set n))
                (if (< n m)
                  (underlying-function (nth funcs (int (/ n 2))))
                  (underlying-function (inv (nth funcs (/ m 2)))))))]
      (->Dependency (unordered-n-pair-preorder arity) nth-set get-function))))

(defmethod to-dependency ChainCopresheaf
  [^ChainCopresheaf chain]

  (->Dependency
    (nth-chain (inc (count (.-functions chain))))
    (fn [i]
      (nth-set-from-source chain i))
    (fn [[a b]]
      (get-chain-transition-function chain a b))))

; Create a dependency copresheaf by a morphism of dependencies
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

(defmethod to-dependency TriangleMorphism
  [^TriangleMorphism morphism]

  (create-dependency-by-morphism
    (to-dependency (source-object morphism))
    (to-dependency (target-object morphism))
    (fn [obj]
      (case obj
        0 (triangle-source-function morphism)
        1 (triangle-middle-function morphism)
        2 (triangle-target-function morphism)))))

(defmethod to-dependency MorphismOfSpans
  [^MorphismOfSpans morphism]

  (create-dependency-by-morphism
    (to-dependency (source-object morphism))
    (to-dependency (target-object morphism))
    (fn [obj]
      (case obj
        0 (span-flag-function morphism)
        1 (span-edge-function morphism)
        2 (span-vertex-function morphism)))))

(defmethod to-dependency MorphismOfCospans
  [^MorphismOfCospans morphism]

  (create-dependency-by-morphism
    (to-dependency (source-object morphism))
    (to-dependency (target-object morphism))
    (fn [obj]
      (case obj
        0 (first-cospan-source-function morphism)
        1 (second-cospan-source-function morphism)
        2 (cospan-target-function morphism)))))

(defmethod to-dependency Cube
  [^Cube morphism]

  (create-dependency-by-morphism
    (to-dependency (source-object morphism))
    (to-dependency (target-object morphism))
    (fn [obj]
      (case obj
        0 (source-input-function morphism)
        1 (source-output-function morphism)
        2 (target-input-function morphism)
        3 (target-output-function morphism)))))

(defmethod to-dependency ChainMorphism
  [^ChainMorphism morphism]

  (create-dependency-by-morphism
    (to-dependency (source-object morphism))
    (to-dependency (target-object morphism))
    (fn [i]
      (nth-chain-morphism-component-function morphism i))))

; Copresheaves over height two total preorders on three objects
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

(defn trijection
  [a b]

  (multijection a b))

; Functions and bijections with adjoined sets
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

; The topos of trisets is the topos Sets^{1+1+1}.
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

; Crown copresheaves as descriptors of relations of sets
(defn crown
  [vertices relation-of-sets]

  (let [first-member-flags (seqable-binary-relation
                             relation-of-sets
                             vertices
                             (fn [[set-pair first-elem]]
                               (contains? (first set-pair) first-elem)))
        second-member-flags (seqable-binary-relation
                              relation-of-sets
                              vertices
                              (fn [[set-pair second-elem]]
                                (contains? (second set-pair) second-elem)))]
    (->Dependency
     two-two-order
     (fn [obj]
       (case obj
         0 first-member-flags
         1 second-member-flags
         2 relation-of-sets
         3 vertices))
     (fn [[i j]]
       (case [[i j]]
         [0 0] (identity-function first-member-flags)
         [1 1] (identity-function second-member-flags)
         [2 2] (identity-function relation-of-sets)
         [3 3] (identity-function vertices)
         [0 2] (->SetFunction first-member-flags relation-of-sets first)
         [0 3] (->SetFunction first-member-flags vertices second)
         [1 2] (->SetFunction second-member-flags relation-of-sets first)
         [1 3] (->SetFunction second-member-flags vertices second))))))

; Copresheaves for generalized incidence structures
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

; Copresheaves in the topos of ditriangles
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

(defn combine-difunctions
  [f g]

  (ditriangle
    (TriangleCopresheaf. (first-function f) (first-function g))
    (TriangleCopresheaf. (second-function f) (second-function g))))

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

(defmethod visualize Dependency
  [^Dependency dependency]

  (let [[p v] (generate-copresheaf-data
                (object-indexed-family dependency)
                (generating-concrete-morphism-triples dependency))]
    (visualize-clustered-digraph* "BT" p v)))