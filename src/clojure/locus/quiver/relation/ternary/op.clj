(ns locus.quiver.relation.ternary.op
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all])
  (:import [locus.base.logic.core.set Universal]))

; A number of mathematical constructions have different representations based upon the
; different topoi that they are embedded in. A binary operation can be expressed either in
; terms of the topoi of sets or functions. It can be expressed as a set of ordered triples
; or a function on ordered pairs. This file provides support for the former representation.
; The later topos is preferable for the study of most algebraic constructions such
; as subobjects and congruences.

; Tupling higher arity relations
(defn tupling-relation
  [rel output-slot-number]

  (set
   (map
    (fn [edge]
      (list
       (map
        (partial nth edge)
        (filter
         (partial not= output-slot-number)
         (range (count edge))))
       (nth edge output-slot-number)))
    rel)))

; Currying higher arity relations
(defn partrel
  [rel & args]

  (if (set? rel)
    (set
     (for [i rel
           :when (= args (take (count args) i))]
       (nthrest i (count args))))
    (let [new-rel (assoc (Universal.
                          (fn [arg]
                            (rel (concat args arg))))
                    :query (fn [arg]
                             ((:query rel)
                              [(vec (concat args (first arg)))
                               (vec (second arg))])))]
      (if (nil? (:arities rel))
        new-rel
        (assoc new-rel
          :arities (set (map dec (:arities rel))))))))

(defn partialize-relation
  [rel]

  (set
   (map
    (fn [i]
      (list i (partrel rel i)))
    (if (set? rel)
      (set (map first rel))
      (:domain rel)))))

(defn departialize-relation
  [rel]

  (apply
   union
   (map
    (fn [[first-elem coll]]
      (if (set? coll)
        (set
         (map
          (fn [i]
            (cons first-elem i))
          coll))
        (fn [i]
          (and
           (= first-elem (first i))
           (coll (rest i))))))
    rel)))

; Operationalize utilities
(defn operationalize
  [rel]

  (partial call rel))

(defn relationalize
  ([func]
   
  (assoc (Universal.
          (fn [coll]
            (and
             (not (empty? coll))
             (let [inputs (if (<= (count coll) 1)
                            (list)
                            (butlast coll))
                   result (last coll)]
               (try
                 (= (apply func inputs) result)
                 (catch Exception e false))))))
    :query (fn [arg]
             (when (empty? (second arg))
               #{(apply func (first arg))}))))
  ([func coll]

   (set (map (fn [i] (list i (func i))) coll)))
  ([func coll arity]

   (set
    (map
     (fn [args] (concat args (list (apply func args))))
     (cartesian-power coll arity)))))

; Operation kernels
(defn operation-kernel
  "Get the kernel of a unary operation"
  [op]

  (let [input-set (set (map first op))
        output-set (set (map second op))]
    (set
     (map
      (fn [output]
        (set
         (filter
          (fn [input]
            (= (query op {0 input}) #{output}))
          input-set)))
      output-set))))

(defn family-of-kernels
  "Get a family of kernels from a general operation"
  [op]

  (if (empty? op)
    #{}
    (let [n (dec (apply max (map count op)))]
      (set
       (map
        (fn [i]
          (operation-kernel
           (set
            (map
             reverse
             (project-relation op #{i n})))))
        (set (range n)))))))

; Infima and suprema
(defn infima-relation
  [order]
  
  (apply
   union
   (map
    (fn [component]
      (intersection
       (cartesian-product
        (vertices component)
        (vertices component)
        (vertices component))
       (fn [[a b c]]
         (contains? (infimum component (set [a b])) c))))
    (weakly-connected-components order))))

(defn suprema-relation
  [order]

  (apply
   union
   (map
    (fn [component]
      (intersection
       (cartesian-product
        (vertices component)
        (vertices component)
        (vertices component))
       (fn [[a b c]]
         (contains? (supremum component (set [a b])) c))))
    (weakly-connected-components order))))

; Antiuniform triples
(defn antiuniform-triples
  [rel]

  (set
   (filter
    (fn [indices]
      (apply
       distinct?
       (map
        (fn [coll]
          (map
           (fn [i]
             (nth coll i))
           indices))
        rel)))
    (power-set (set (range 3))))))

; Specific types of elements
(defn idempotent-elements
  [op]

  (set
    (filter
      (fn [i]
        (= (call op i i) i))
      (vertices op))))

(defn left-zero-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel i j)
               i))
          (vertices rel)))
      (vertices rel))))

(defn left-unital-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel i j)
               j))
          (vertices rel)))
      (vertices rel))))

(defn right-zero-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel j i)
               i))
          (vertices rel)))
      (vertices rel))))

(defn right-unital-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel i j)
               j))
          (vertices rel)))
      (vertices rel))))

(defn central-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel i j)
               (call rel j i)))
          (vertices rel)))
      (vertices rel))))

(defn zero-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel i j)
               (call rel j i)
               i))
          (vertices rel)))
      (vertices rel))))

(defn unital-elements
  [rel]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (= (call rel i j)
               (call rel j i)
               j))
          (vertices rel)))
      (vertices rel))))

; Special types of subsets
(defn reachability-closure
  [rel elems]

  (let [current-targets (union
                          elems
                          (apply
                            union
                            (map
                              (fn [[x y]]
                                (union
                                  (query rel {0 x, 1 y})
                                  (query rel {0 y, 1 x})))
                              (cartesian-product
                                (vertices rel)
                                elems))))]
    (if (= current-targets elems)
      elems
      (reachability-closure rel current-targets))))

(defn singleton-closure
  [op i]

  (letfn [(find-elems [current-elem coll]
            (let [new-elem (call op i current-elem)]
              (if (contains? coll new-elem)
                coll
                (find-elems new-elem (union coll #{new-elem})))))]
    (find-elems i #{i})))

(defn operational-closure
  [op coll]

  (let [new-elems (set
                    (map
                      (fn [[a b]]
                        (call op a b))
                      (cartesian-power coll 2)))]
    (if (superset? (list new-elems coll))
      coll
      (operational-closure op (union coll new-elems)))))

(defn closed-suboperators
  [rel]

  (set
    (filter
      (fn [elems]
        (every?
          (fn [coll]
            (or
              (contains? elems (last coll))
              (not (superset? (list (set (butlast coll)) elems)))))
          rel))
      (power-set (vertices rel)))))

(defn singleton-closures
  [rel]

  (set
    (map
      (fn [i]
        (singleton-closure rel i))
      (vertices rel))))

(defn reachability-closures
  [rel]

  (set
    (map
      (fn [i]
        (reachability-closure rel #{i}))
      (vertices rel))))

(defn commutative-pair?
  [rel a b]

  (= (call rel a b)
     (call rel b a)))

(defn commutative-pairs
  [rel]

  (union
    (set (map (fn [i] #{i}) (vertices rel)))
    (set
      (filter
        (fn [pair]
          (let [[a b] (seq pair)]
            (= (call rel a b)
               (call rel b a))))
        (selections (vertices rel) 2)))))

; Relations constructed from the operation
(defn operational-domain
  [rel]

  (project-relation rel #{0 1}))

(defn left-neutrality
  [op]

  (set
    (filter
      (fn [[a b]]
        (= (call op a b) b))
      (cartesian-product (vertices op) (vertices op)))))

(defn right-neutrality
  [op]

  (set
    (filter
      (fn [[a b]]
        (= (call op a b) a))
      (cartesian-product (vertices op) (vertices op)))))

(defn neutrality
  [op]

  (set
    (filter
      (fn [[a b]]
        (or (= (call op a b) (call op b a) a)
            (= (call op a b) (call op b a) b)))
      (cartesian-product (vertices op) (vertices op)))))

(defn algebraic-preorder
  [rel]

  (intersection
    (fn [[a b]]
      (superset?
        (list (reachability-closure rel #{b}) (reachability-closure rel #{a}))))
    (cartesian-product (vertices rel) (vertices rel))))

; Suboperators
(defn internally-closed-suboperators
  [op]

  (set
    (filter
      (fn [coll]
        (every?
          (fn [[x y]]
            (contains? coll (call op x y)))
          (cartesian-product coll coll)))
      (power-set (vertices op)))))

(defn externally-closed-suboperators
  [op]

  (set
    (filter
      (fn [coll]
        (every?
          (fn [[internal-element external-element]]
            (and
              (contains? coll (call op internal-element external-element))
              (contains? coll (call op external-element internal-element))))
          (cartesian-product coll (vertices op))))
      (power-set (vertices op)))))

(defn magma-relation-by-table
  [coll]

  (apply
    union
    (map
      (fn [i]
        (set
          (map
            (fn [j]
              (list i j (nth (nth coll i) j)))
            (range (count coll)))))
      (range (count coll)))))

; Ternary relations
(def ternary-relation?
  (power-set size-three-seq?))

; Basic binary operations
(def single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})))

(def backwards-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{1 2} #{0})))

(def center-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 2} #{1})))

(def inverse-backwards-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0} #{1})
    (functional-dependency #{0} #{2})))

(def inverse-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{2} #{0})
    (functional-dependency #{2} #{1})))

(def inverse-center-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{1} #{0})
    (functional-dependency #{1} #{2})))

; Reversible binary operations
(def reversible-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})
    (functional-dependency #{2} #{0 1})))

(def reversible-center-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 2} #{1})
    (functional-dependency #{1} #{0 2})))

(def reversible-backwards-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{1 2} #{0})
    (functional-dependency #{0} #{1 2})))

; Additional classes of binary operations
(def center-cancellative-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})
    (functional-dependency #{0 2} #{1})))

(def bidirectional-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})
    (functional-dependency #{1 2} #{0})))

(def center-cancellative-backwards-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{1 2} #{0})
    (functional-dependency #{0 2} #{1})))

(def cancellative-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})
    (functional-dependency #{0 2} #{1})
    (functional-dependency #{1 2} #{0})))

; Sectional
(def front-sectional-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0} #{1 2})
    (functional-dependency #{1} #{0 2})))

(def back-sectional-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{2} #{0 1})
    (functional-dependency #{1} #{0 2})))

(def outer-sectional-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0} #{1 2})
    (functional-dependency #{2} #{0 1})))

(def one-to-one-to-one-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0} #{1 2})
    (functional-dependency #{1} #{0 2})
    (functional-dependency #{2} #{0 1})))

(def unique-ternary-relation?
  (intersection
    unique-universal?
    ternary-relation?))

; Partially functional relations
(def left-invariant-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{1} #{2})))

(def right-invariant-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0} #{2})))

(def constant-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{} #{2})))

(def left-reversible-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})
    (functional-dependency #{2} #{0})))

(def right-reversible-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0 1} #{2})
    (functional-dependency #{2} #{1})))

(def left-invariant-right-reversible-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{1} #{2})
    (functional-dependency #{2} #{1})))

(def right-invariant-left-reversible-single-valued-ternary-relation?
  (intersection
    ternary-relation?
    (functional-dependency #{0} #{2})
    (functional-dependency #{2} #{0})))

; Conditions not related to functional dependencies
(def anticommutative-single-valued-ternary-relation?
  (intersection
    single-valued-ternary-relation?
    (fn [rel]
      (every?
        (fn [i]
          (not (rel (list (second i) (first i) (last i)))))
        rel))))

; Extra functions
(defn commutative-single-valued-ternary-relation?
  [rel]
  (= (commutative-pairs rel)
     (multiselection (vertices rel) #{1 2})))

(defn associative-single-valued-ternary-relation?
  [rel]

  (let [op (partial call rel)
        vertices (vertices rel)]
    (or
      (empty? vertices)
      (every?
        (fn [[x y z]]
          (= (op (op x y) z)
             (op x (op y z))))
        (cartesian-product vertices vertices vertices)))))

(defn unital-single-valued-ternary-relation?
  [rel]

  (not
    (every?
      (complement
        (fn [i]
          (every?
            (fn [j]
              (= (call rel i j) (call rel j i) j))
            (vertices rel))))
      (vertices rel))))

(defn idempotent-single-valued-ternary-relation?
  [rel]

  (every?
    (fn [vertex]
      (= (query rel {0 vertex, 1 vertex}) #{vertex}))
    (vertices rel)))

; Magma relations
(def magma-relation?
  (intersection
    single-valued-ternary-relation?
    (fn [rel] (total-on? rel #{0 1}))))

(defn quasigroup-relation?
  [rel]

  (and
    (magma-relation? rel)
    (every?
      (fn [[a b]]
        (= 1
           (count
             (filter
               (fn [i]
                 (= (call rel a i) b))
               (vertices rel)))
           (count
             (filter
               (fn [i]
                 (= (call rel i a) b))
               (vertices rel)))))
      (cartesian-product (vertices rel) (vertices rel)))))

(def moufang-loop-relation?
  (intersection
    quasigroup-relation?
    unital-single-valued-ternary-relation?
    (fn [rel]
      (every?
        (fn [[x y z]]
          (let [op (partial call rel)]
            (and
              (= (op z (op x (op z y)))
                 (op (op (op z x) z) y))
              (= (op x (op z (op y z)))
                 (op (op (op x z) y) z))
              (= (op (op z x) (op y z))
                 (op z (op (op x y) z))))))
        (cartesian-product (vertices rel) (vertices rel) (vertices rel))))))

(defn monogenic-semigroup-relation?
  [op]

  (and
    (magma-relation? op)
    (associative-single-valued-ternary-relation? op)
    (not
      (every?
        (complement
          (fn [i]
            (= (singleton-closure op i) (vertices op))))
        (vertices op)))))

(def null-semigroup-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    (fn [rel]
      (not
        (every?
          (complement
            (fn [zero-element]
              (every?
                (fn [i]
                  (and
                    (= (call rel i zero-element) zero-element)
                    (= (call rel zero-element i) zero-element)))
                (vertices rel))))
          (vertices rel))))))

(def regular-semigroup-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    (fn [op]
      (every?
        (fn [vertex]
          (not
            (every?
              (complement
                (fn [psuedoinverse]
                  (= (call op vertex (call op psuedoinverse vertex))
                     vertex)))
              (vertices op))))
        (vertices op)))))

(def completely-regular-semigroup-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    (fn [rel]
      (every?
        (fn [i]
          ((intersection
             quasigroup-relation?
             unital-single-valued-ternary-relation?)
           (subrelation
             rel
             (singleton-closure rel i))))
        (vertices rel)))))

(def inverse-semigroup-relation?
  (intersection
    regular-semigroup-relation?
    (fn [op]
      (let [idempotents (idempotent-elements op)]
        (every?
          (fn [[a b]]
            (commutative-pair? op a b))
          (cartesian-power idempotents 2))))))

(def rectangular-band-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    idempotent-single-valued-ternary-relation?
    (fn [op]
      (every?
        (fn [[x y]]
          (= (call op (call op x y) x) x))
        (cartesian-product (vertices op) (vertices op))))))

(def orthodox-semigroup-relation?
  (intersection
    regular-semigroup-relation?
    (fn [rel]
      (let [idempotent-elements (set
                                  (filter
                                    (fn [i]
                                      (= (call rel i i) i))
                                    (vertices rel)))]
        (every?
          (fn [[x y]]
            (contains? idempotent-elements (call rel x y)))
          (cartesian-product idempotent-elements idempotent-elements))))))

(def medial-magma-relation?
  (intersection
    magma-relation?
    (fn [rel]
      (let [op (partial call rel)
            coll (vertices rel)]
        (every?
          (fn [[x y u v]]
            (= (op (op x y) (op u v))
               (op (op x u) (op y v))))
          (cartesian-product coll coll coll coll))))))

(def normal-band-relation?
  (intersection
    magma-relation?
    idempotent-single-valued-ternary-relation?
    (fn [rel]
      (let [op (partial call rel)
            coll (vertices rel)]
        (every?
          (fn [[x y z]]
            (= (op x (op y (op z x)))
               (op x (op z (op y x)))))
          (cartesian-product coll coll coll))))))

(def medial-semigroup-relation?
  (intersection
    medial-magma-relation?
    associative-single-valued-ternary-relation?))

(def semigroup-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?))

(def monoid-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    unital-single-valued-ternary-relation?))

(def commutative-magma-relation?
  (intersection
    commutative-single-valued-ternary-relation?
    magma-relation?))

(def commutative-semigroup-relation?
  (intersection
    commutative-single-valued-ternary-relation?
    semigroup-relation?))

(def clifford-semigroup-relation?
  (intersection
    inverse-semigroup-relation?
    completely-regular-semigroup-relation?))

(def commutative-clifford-semigroup-relation?
  (intersection
    commutative-single-valued-ternary-relation?
    completely-regular-semigroup-relation?))

(def commutative-monoid-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    unital-single-valued-ternary-relation?
    commutative-single-valued-ternary-relation?))

(def directoid-relation?
  (intersection
    magma-relation?
    idempotent-single-valued-ternary-relation?))

(def band-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    idempotent-single-valued-ternary-relation?))

(def semilattice-relation?
  (intersection
    magma-relation?
    commutative-single-valued-ternary-relation?
    associative-single-valued-ternary-relation?
    idempotent-single-valued-ternary-relation?))

(def unital-band-relation?
  (intersection
    magma-relation?
    associative-single-valued-ternary-relation?
    idempotent-single-valued-ternary-relation?
    unital-single-valued-ternary-relation?))

(def unital-semilattice-relation?
  (intersection
    magma-relation?
    commutative-single-valued-ternary-relation?
    associative-single-valued-ternary-relation?
    idempotent-single-valued-ternary-relation?
    unital-single-valued-ternary-relation?))

(def loop-relation?
  (intersection
    quasigroup-relation?
    unital-single-valued-ternary-relation?))

(def group-relation?
  (intersection
    quasigroup-relation?
    unital-single-valued-ternary-relation?
    associative-single-valued-ternary-relation?))

(def abelian-group-relation?
  (intersection
    quasigroup-relation?
    unital-single-valued-ternary-relation?
    associative-single-valued-ternary-relation?
    commutative-single-valued-ternary-relation?))

(def cyclic-group-relation?
  (intersection
    group-relation?
    monogenic-semigroup-relation?))



