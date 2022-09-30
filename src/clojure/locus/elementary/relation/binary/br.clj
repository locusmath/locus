(ns locus.elementary.relation.binary.br
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all])
  (:import [locus.base.logic.core.set Universal]
           [locus.elementary.relation.binary.sr SeqableRelation]
           [locus.elementary.relation.binary.product CompleteRelation BinaryCartesianProduct]))

; This file contains our basic ontology of binary relations. This ontology extends the classical
; ontology with an original and independently developed set of classes of binary relations which
; is based upon set theoretic metaproperties of the classes: such as the classification of binary
; relations into Moore families, subclass closed families, etc. This is similar to the classification of
; algebraic structures based upon varieties and other meta-properties. The different meta-property classes
; of relations typically form their own lattices which are embedded in one way or another in
; the total boolean algebra of all classes of relations.

; Transposition is one of the fundamental objects of relation theory
(defmulti transpose
  (fn [a] (type a)))

(defmethod transpose CompleteRelation
  [a] a)

(defmethod  transpose BinaryCartesianProduct
  [a]

  (BinaryCartesianProduct.
   (relation-codomain a)
   (relation-domain a)))

(defmethod transpose SeqableRelation
  [a]

  (SeqableRelation.
   (vertices a)
   (fn [pair]
     (a (reverse pair)))
   (if (nil? (:count (.attrs a)))
     {}
     {:count (:count (.attrs a))})))

(defmethod transpose :default
  [coll]

  (if (set? coll)
    (set
     (for [i coll
           :when (seq? i)]
       (reverse i)))
    (let [pred (fn [arg]
                 (or
                  (and (not (seq? arg)) (coll arg))
                  (coll (reverse arg))))]
      (if (nil? (:query coll))
        pred
        (assoc (Universal. pred)
               :query (fn [arg]
                        ((:query coll) [(vec (reverse (second arg)))
                                        (vec (reverse (first arg)))])))))))

; Queries
(defn query
  [rel arg]

  (let [size (inc (count (keys arg)))
        first-missing-index (apply
                             min
                             (clojure.set/difference
                              (set (range size))
                              (set (keys arg))))]
    (if (seqable-universal? rel)
      (set
       (for [coll rel
             :when (and (= (count coll) size)
                        (every?
                         (fn [i]
                           (= (nth coll i) (get arg i)))
                         (keys arg)))]
         (nth coll first-missing-index)))
      ((:query rel)
       (if (= size 1)
         [[] []]
         [(vec (map arg (range 0 first-missing-index)))
          (vec (map arg (range (inc first-missing-index) size)))])))))

; Calls
(defn call
  [rel & args]

  (first
   (query
    rel
    (zipmap
     (set (range (count args)))
     args))))

; Convert a relation to an adjacency list
(defn to-adjacency-list
  [rel]

  (loop [rval {}
         remaining-elements (seq rel)]
    (if (empty? remaining-elements)
      rval
      (recur
        (let [elem (first remaining-elements)
              k (first elem)
              v (second elem)]
          (assoc rval k (conj (get rval k) v)))
        (rest remaining-elements)))))

; Images and pre images
(defn relation-image
  [rel coll]

  (apply
   union
   (map
    (fn [i]
      (direct-successors rel i))
    coll)))

(defn preimage
  [rel coll]

  (apply
   union
   (map
    (fn [i]
      (direct-predecessors rel i))
    coll)))

(defn multi-image
  [rel coll]

  (apply
   add
   (map
    (fn [i]
      (direct-successors rel i))
    coll)))

(defn multi-preimage
  [rel coll]

  (apply
   add
   (map
    (fn [i]
      (direct-predecessors rel i))
    coll)))

; Composition
(defn compose-relations
  ([r] r)
  ([r s]
   (set
    (for [[[a b] [c d]] (cartesian-product r s)
          :when (= d a)]
      (list c b))))
  ([a b & more]
   (reduce compose-relations (compose-relations a b) more)))

; Essential functions
(defn irreversibility
  [rel]

  (repetitiveness (multicodomain rel)))

(defn multivaluedness
  [rel]

  (repetitiveness (multidomain rel)))

; Functional dependencies
(defn satisfies-functional-dependency?
  "This is the main method used for testing for functional dependencies."
  [rel source-slots target-slots]

  (letfn [(singular? [coll]
            (= 1 (count coll)))
          (sublist [coll elems]
            (vec
              (map
                (vec coll)
                elems)))]
    (if (empty? source-slots)
      (equal-seq?
        (map
          (fn [elem]
            (sublist elem target-slots))
          rel))
      (every?
        (fn [source]
          (singular?
            (set
              (for [elem rel
                    :when (= (sublist elem source-slots) source)]
                (sublist elem target-slots)))))
        (map
          (fn [elem]
            (sublist elem source-slots))
          rel)))))

(defn functional-dependency
  "This takes a functional dependency and produces a predicate from it."
  [source-slots target-slots]

  (fn [rel]
    (satisfies-functional-dependency? rel source-slots target-slots)))

(defn functionally-dependent?
  "We can treat functional dependency as a binary relation."
  [source-slots target-slots first-edge second-edge]

  (letfn [(sublist [coll indexes]
            (vec
              (map
                (vec coll)
                indexes)))]
    (or
     (not= (sublist first-edge source-slots) (sublist second-edge source-slots))
     (= (sublist first-edge target-slots) (sublist second-edge target-slots)))))

; Restrict relations
(defn subrelation
  [rel coll]

  (if (and
       (universal? rel)
       (set? (:arities rel)))
    (intersection
     rel
     (apply
      union
      (map
       (fn [n]
         (apply cartesian-product (repeat n coll)))
       (:arities rel))))
    (intersection
     rel
     seq?
     (partial every? coll))))

(defn subrelations
  [pred? rel]

  (set
   (filter
    (fn [coll]
      (pred? (subrelation rel coll)))
    (power-set (vertices rel)))))

; Binary subrelations only
(defn binary-subrelation
  [rel coll]

  (set (filter rel (complete-relation coll))))

; Restrict a relation by slots
(defn restrict-slot-values
  [rel index val]

  (set
   (filter
    (fn [coll]
      (= (nth coll index) val))
    rel)))

; Restrict the members of the relation
(defn project-relation
  [rel nums]

  (set
   (map
    (fn [coll]
      (map
       (fn [i]
         (nth coll i))
       nums))
    rel)))

(defn get-slot-values
  [rel num]

  (set (map (fn [coll] (nth coll num)) rel)))

(defn total-on?
  [rel slots]

  (= (cartesian-power
      (vertices rel)
      (count slots))
     (project-relation rel slots)))

; Constructors for relations with querying applications
(defn backwards-relation
  [coll func]

  (assoc (Universal.
          coll)
    :arities #{2}
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[a] []] arg]
                       (fn [i]
                         (coll (list a i))))
               [0 1] (let [[[] [b]] arg]
                       (func b))
               #{}))))

(defn forwards-relation
  [coll func]

  (assoc (Universal.
          coll)
    :arities #{2}
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[a] []] arg]
                       (func a))
               [0 1] (let [[[] [b]] arg]
                       (fn [i]
                         (coll (list i b))))
               #{}))))

(defn bidirectional-relation
  [coll forwards-func backwards-func]

  (assoc (Universal.
          coll)
    :arities #{2}
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[a] []] arg]
                       (forwards-func a))
               [0 1] (let [[[] [b]] arg]
                       (backwards-func b))
               #{}))))

; Vertex partitions
(defn domain-partition
  [rel]

  (let [domain (relation-domain rel)
        distinct-outputs (set (map (partial direct-successors rel) domain))]
    (set
     (map
      (fn [output]
        (set
         (filter
          (fn [i]
            (= (direct-successors rel i) output))
          domain)))
      distinct-outputs))))

(defn codomain-partition
  [rel]

  (let [codomain (relation-codomain rel)
        distinct-inputs (set (map (partial direct-predecessors rel) codomain))]
    (set
     (map
      (fn [input]
        (set
         (filter
          (fn [i]
            (= (direct-predecessors rel i) input))
          codomain)))
      distinct-inputs))))

(defn vertex-equality
  [rel]

  (pn
   (fn [a b]
     (and
      (= (direct-successors rel a) (direct-successors rel b))
      (= (direct-predecessors rel a) (direct-predecessors rel b))))
   (vertices rel)))

; Connectivity test
(defn weak-connectivity
  [rel]

  (letfn [(independent? [a b]
            (= 0 (pair-degree rel [a b])))
          (get-new-dependents [unchecked-elems checked-elems]
            (set
             (filter
              (fn [unchecked-elem]
                (not
                 (every?
                  (fn [elem]
                    (independent? elem unchecked-elem))
                  checked-elems)))
              unchecked-elems)))
          (get-dependent-component [unchecked-elems checked-elems]
            (let [new-dependents (get-new-dependents unchecked-elems checked-elems)]
              (if (empty? new-dependents)
                checked-elems
                (get-dependent-component
                 (difference unchecked-elems new-dependents)
                 (union checked-elems new-dependents)))))
          (get-dependent-components [coll]
            (if (empty? coll)
              #{}
              (let [first-index (first coll)
                    current-component (get-dependent-component
                                       (difference coll #{first-index})
                                       #{first-index})]
                (union
                 #{current-component}
                 (get-dependent-components (difference coll current-component))))))]
    (get-dependent-components (vertices rel))))

(defn weakly-connected-components
  [rel]

  (set
   (map
    (partial subrelation rel)
    (weak-connectivity rel))))

(defn every-component?
  [pred? rel]

  (every?
   pred?
   (weakly-connected-components rel)))

; Strong connectivity
(defn strong-connectivity
  [rel]

  (letfn [(get-targets [rel added to-add]
            (if (clojure.set/subset? to-add added)
              added
              (get-targets
               rel
               (union added to-add)
               (apply
                union
                (map
                 (fn [i]
                   (set
                    (for [coll rel
                          :when (and
                                 (seq? coll)
                                 (= (count coll) 2)
                                 (= (first coll) i))]
                      (second coll))))
                 to-add)))))
          (find-component [rel transpose-rel vertex]
            (intersection
             (get-targets rel #{} #{vertex})
             (get-targets transpose-rel #{} #{vertex})))
          (find-components [rel transpose-rel unchecked-nodes]
            (if (empty? unchecked-nodes)
              #{}
              (let [current-component (find-component rel transpose-rel (first unchecked-nodes))]
                (union
                 #{current-component}
                 (find-components
                  rel
                  transpose-rel
                  (clojure.set/difference unchecked-nodes current-component))))))]
    (find-components rel (transpose rel) (vertices rel))))

(defn condensation
  [order]

  (let [components (strong-connectivity order)]
    (intersection
     (fn [[a b]]
       (not
        (every?
         (complement
          (fn [i]
            (not
             (every?
              (complement
               (fn [j]
                 (order (list i j))))
              b))))
         a)))
     (cartesian-product components components))))

; Classes of relations
; The ontology of binary relations including special classes
; such as single valued binary relations, symmetric binary
; relations, and so on.
(def relation?
  (power-set seq?))

(def nary-relation?
  (intersection
   (power-set seq?)
   (fn [rel]
     (or
      (empty? rel)
      (apply = (map count rel))))))

(defn single-valued-relation?
  [rel]

  (every?
   (fn [arguments]
     (let [inputs (if (= (count arguments) 1)
                    (list)
                    (butlast arguments))]
       (and
        (not (empty? arguments))
        (every?
         (fn [coll]
           (or
            (not= (count coll) (count arguments))
            (not= (take (count inputs) coll) inputs)
            (= coll arguments)))
         rel))))
   rel))

(def single-valued-nary-relation?
  (intersection
   single-valued-relation?
   nary-relation?))

(def reversible-nary-relation?
  (intersection
    single-valued-nary-relation?
    (fn [rel]
      (every?
        (fn [vertex]
          (<=
            (count
              (filter
                (fn [edge]
                  (= (last edge) vertex))
                rel))
            1))
        (vertices rel)))))

; Classes of binary relations
; The ontology of binary relations has two main basic meta-components: a theory of
; Moore families and a theory of subclass closed families of binary relations.
; These two meta-properties determine the position that a given class of binary
; relations must take within the set theoretic ontology.
(def binary-relation?
  (power-set size-two-seq?))

(def irreflexive?
  (power-set distinct-size-two-seq?))

(def coreflexive?
  (power-set equal-size-two-seq?))

(def size-two-binary-relation?
  (intersection
    binary-relation?
    size-two-universal?))

(def size-three-binary-relation?
  (intersection
    binary-relation?
    size-three-universal?))

(def size-four-binary-relation?
  (intersection
    binary-relation?
    size-four-universal?))

; Height two
(def height-two?
  (intersection
   binary-relation?
   (fn [rel]
     (every?
      (complement
       (fn [[a b]]
         (and
          (not= (first a) (second b))
          (= (second a) (first b))
          (apply distinct? a)
          (apply distinct? b))))
      (cartesian-product rel rel)))))

; Anti-uniform set
(defn antisymmetric?
  [rel]

  (and
   (binary-relation? rel)
   (every?
    (fn [[a b]]
      (or
       (= a b)
       (not (and (rel (list a b)) (rel (list b a))))))
    (cartesian-power (vertices rel) 2))))

; Slot distinctiveness relations
(def single-valued-binary-relation?
  (intersection
   binary-relation?
   (functional-dependency #{0} #{1})))

(def inverse-single-valued-binary-relation?
  (intersection
   binary-relation?
   (functional-dependency #{1} #{0})))

(def reversible-binary-relation?
  (intersection
   binary-relation?
   (functional-dependency #{0} #{1})
   (functional-dependency #{1} #{0})))

(defn unique-binary-relation?
  [rel]

  (and
   (binary-relation? rel)
   (<= (count rel) 1)))

; Antisymmetric versions
(def antisymmetric-single-valued-binary-relation?
  (intersection
   antisymmetric?
   single-valued-binary-relation?))

(def antisymmetric-inverse-single-valued-binary-relation?
  (intersection
   antisymmetric?
   inverse-single-valued-binary-relation?))

(def antisymmetric-reversible-binary-relation?
  (intersection
   antisymmetric?
   reversible-binary-relation?))

; Height two versions
(def height-two-single-valued-binary-relation?
  (intersection
   height-two?
   single-valued-binary-relation?))

(def height-two-inverse-single-valued-binary-relation?
  (intersection
   height-two?
   inverse-single-valued-binary-relation?))

(def height-two-reversible-binary-relation?
  (intersection
   height-two?
   reversible-binary-relation?))

(def near-idempotent-single-valued-binary-relation?
  (intersection
   antisymmetric?
   height-two?
   single-valued-binary-relation?))

(def near-idempotent-inverse-single-valued-binary-relation?
  (intersection
   antisymmetric?
   height-two?
   inverse-single-valued-binary-relation?))

(def fully-independent-reversible-binary-relation?
  (intersection
   antisymmetric?
   height-two?
   reversible-binary-relation?))

; Constant unary operations
(def constant-single-valued-binary-relation?
  (intersection
   binary-relation?
   (functional-dependency #{} #{1})))

(def inverse-constant-single-valued-binary-relation?
  (intersection
   binary-relation?
   (functional-dependency #{} #{0})))

; Acyclic functions
(def acyclic-single-valued-binary-relation?
  (intersection
   single-valued-binary-relation?
   (fn [i]
     (every? singular-universal? (strong-connectivity i)))))

(defn multichain-single-valued-binary-relation?
  [rel]

  (and
   (acyclic-single-valued-binary-relation? rel)
   (reversible-binary-relation?
    (intersection distinct-size-two-seq? rel))))

(def chain-single-valued-binary-relation?
  (intersection
   multichain-single-valued-binary-relation?
   (fn [rel] (<= (count (weak-connectivity rel)) 1))))

; Special functionality for dealing with transformation relations
(defn totalize
  [op]

  (union
   op
   (coreflexive-relation
    (set
     (filter
      (fn [i]
        (empty? (direct-successors op i)))
      (vertices op))))))

(def transformation-relation?
  (intersection
   single-valued-binary-relation?
   (fn [rel] (total-on? rel #{0}))))

(def acyclic-transformation-relation?
  (intersection
   acyclic-single-valued-binary-relation?
   (fn [rel] (total-on? rel #{0}))))

(def idempotent-transformation-relation?
  (intersection
   single-valued-binary-relation?
   antisymmetric?
   height-two?
   (fn [rel] (total-on? rel #{0}))))

(def constant-transformation-relation?
  (intersection
   constant-single-valued-binary-relation?
   (fn [rel] (total-on? rel #{0}))))

; Create permutation relations
(defn permutation-relation
  [perm]

  (apply
   union
   (map
    (fn [coll]
      (if (= (count coll) 1)
        #{(list (first coll) (first coll))}
        (set
         (map
          (fn [i]
            (if (= i (dec (count coll)))
              (list (nth coll i) (first coll))
              (list (nth coll i) (nth coll (inc i)))))
          (range (count coll))))))
    perm)))

(def permutation-relation?
  (intersection
   reversible-binary-relation?
   (fn [rel] (total-on? rel #{0}))))

(def derangement-permutation-relation?
  (intersection
   permutation-relation?
   irreflexive?))

(def involution-permutation-relation?
  (intersection
   permutation-relation?
   height-two?))

(def cyclic-permutation-relation?
  (intersection
   permutation-relation?
   (fn [rel] (<= (count (weak-connectivity rel)) 1))))

; Disjoint edge conditions
(defn loop-unique?
  [rel]

  (every?
   (fn [pair]
     (not (every? equal-seq? pair)))
   (selections rel 2)))

(defn loop-edge-antidisjoint?
  [rel]

  (every?
   (complement
    (fn [[a b]]
      (and
       (equal-seq? a)
       (distinct-seq? b)
       (empty? (intersection (set a) (set b))))))
   (cartesian-product rel rel)))

(defn edge-antidisjoint?
  [rel]

  (every?
   (complement
    (fn [[a b]]
      (and
       (distinct-seq? a)
       (distinct-seq? b)
       (empty? (intersection (set a) (set b))))))
   (cartesian-product rel rel)))

; Irreflexive conditions
(defn irreflexive-predecessors?
  [rel]

  (every?
   (fn [i]
     (or
      (equal-seq? i)
      (not (contains? rel (list (first i) (first i))))))
   rel))

(defn irreflexive-successors?
  [rel]

  (every?
   (fn [i]
     (or
      (equal-seq? i)
      (not (contains? rel (list (second i) (second i))))))
   rel))

; Higher conditions
(defn unique-output?
  [rel]

  (every?
   (complement
    (fn [[a b]]
      (and
       (distinct-seq? a)
       (distinct-seq? b)
       (not= (first a) (first b)))))
   (cartesian-product rel rel)))

(defn unique-input?
  [rel]

  (every?
   (complement
    (fn [[a b]]
      (and
       (distinct-seq? a)
       (distinct-seq? b)
       (not= (first a) (first b)))))
   (cartesian-product rel rel)))

; Additional types
(comment
  (defn fully-antidisjoint?
    [rel]

    (antidisjoint-family? (set (map set rel)))))

(def loop-isolated?
  (intersection
   irreflexive-predecessors?
   irreflexive-successors?))

(def asymmetric?
  (intersection
   irreflexive?
   antisymmetric?))

(def antidependency?
  (intersection
   loop-isolated?
   antisymmetric?))

(def loop-isolated-height-two?
  (intersection
   loop-isolated?
   height-two?))

(def antisymmetric-height-two?
  (intersection
   antisymmetric?
   height-two?))

(def antidependency-height-two?
  (intersection
   antisymmetric?
   loop-isolated?
   height-two?))

; Irreflexivity conditions
(defn partially-irreflexive?
  [rel]

  (every?
   (fn [i]
     (or
      (equal-size-two-seq? i)
      (let [[a b] (seq i)]
        (or
         (not (rel (list a a)))
         (not (rel (list b b)))))))
   rel))

(defn irreflexive-symmetric-component?
  [rel]

  (every?
   (fn [i]
     (or
      (equal-size-two-seq? i)
      (let [[a b] (seq i)]
        (or
         (not (rel (list b a)))
         (and
          (not (rel (list a a)))
          (not (rel (list b b))))))))
   rel))

(defn irreflexive-center?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (second a) (first b))
       (rel (list (second a) (second a))))))
   (cartesian-product rel rel)))

(defn irreflexive-far-predecessors?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (second a) (first b))
       (rel (list (first a) (first a))))))
   (cartesian-product rel rel)))

(defn irreflexive-far-successors?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (second a) (first b))
       (rel (list (second b) (second b))))))
   (cartesian-product rel rel)))

(defn irreflexive-common-predecessors?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (second a) (second b))
       (rel (list (second a) (second a))))))
   (cartesian-product rel rel)))

(defn irreflexive-common-succcessors?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (first a) (first b))
       (rel (list (first a) (first b))))))
   (cartesian-product rel rel)))

(defn irreflexive-multiple-predecessors?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (second a) (second b))
       (not
        (or
         (rel (list (first a) (first a)))
         (rel (list (first b) (first b))))))))
   (cartesian-product rel rel)))

(defn irreflexive-multiple-successors?
  [rel]

  (every?
   (fn [[a b]]
     (not
      (and
       (not= (set a) (set b))
       (distinct-seq? a)
       (distinct-seq? b)
       (= (first a) (first b))
       (not
        (or
         (rel (list (second a) (second a)))
         (rel (list (second b) (second b))))))))
   (cartesian-product rel rel)))

; Antisymmetric conditions
(def antisymmetric-predecessors?
  (intersection
   binary-relation?
   (fn [rel]
     (every?
      (fn [[a b]]
        (not
         (and
          (not= (set a) (set b))
          (distinct-seq? a)
          (distinct-seq? b)
          (= (second a) (first b))
          (rel (list (second a) (first a))))))
      (cartesian-product rel rel)))))

(def antisymmetric-successors?
  (intersection
   binary-relation?
   (fn [rel]
     (every?
      (fn [[a b]]
        (not
         (and
          (not= (set a) (set b))
          (distinct-seq? a)
          (distinct-seq? b)
          (= (second a) (first b))
          (rel (list (second b) (first b))))))
      (cartesian-product rel rel)))))

; Conditions on pairs
(def edge-antitransitive?
  (intersection
   binary-relation?
   (fn [rel]
     (every?
      (fn [[a b]]
        (not
         (and
          (not= a b)
          (distinct-seq? a)
          (distinct-seq? b)
          (= (second a) (first b))
          (rel (list (first a) (second b))))))
      (cartesian-product rel rel)))))

(def edge-anticircular?
  (intersection
   binary-relation?
   (fn [rel]
     (every?
      (fn [[a b]]
        (not
         (and
          (not= a b)
          (rel (list (second b) (first a))))))
      (cartesian-product rel rel)))))

; Chain conditions
(defn height-three?
  [rel]

  (every?
   (fn [[a b c]]
     (not
      (and
       (not= (set a) (set b))
       (not= (set b) (set c))
       (not= (set a) (set c))
       (every? distinct-seq? [a b c])
       (= (second a) (first b))
       (= (second b) (first c)))))
   (cartesian-power rel 3)))

(defn reverse-edge-between-free?
  [rel]

  (every?
   (fn [[a b c]]
     (not
      (and
       (not= (set a) (set b))
       (not= (set b) (set c))
       (not= (set a) (set c))
       (every? distinct-seq? [a b c])
       (= (second a) (second b))
       (= (first b) (first c)))))
   (cartesian-power rel 3)))

(defn pair-output-free?
  [rel]

  (every?
   (fn [[a b c]]
     (not
      (and
       (not= (set a) (set b))
       (not= (set b) (set c))
       (not= (set a) (set c))
       (every? distinct-seq? [a b c])
       (= (second a) (first b))
       (= (second c) (second b)))))
   (cartesian-power rel 3)))

(defn pair-input-free?
  [rel]

  (every?
   (fn [[a b c]]
     (not
      (and
       (not= (set a) (set b))
       (not= (set b) (set c))
       (not= (set a) (set c))
       (every? distinct-seq? [a b c])
       (= (first a) (first b))
       (= (first c) (second b)))))
   (cartesian-power rel 3)))

; Proper in and out degree
(defn max-proper-in-degree-two?
  [rel]

  (every?
   (fn [i]
     (<= (proper-in-degree rel i) 2))
   (vertices rel)))

(defn max-proper-out-degree-two?
  [rel]

  (every?
   (fn [i]
     (<= (proper-out-degree rel i) 2))
   (vertices rel)))

(defn terminal-common-predecessors?
  [rel]

  (every?
   (fn [i]
     (or
      (not (<= (proper-in-degree rel i) 2))
      (= (proper-out-degree rel i) 0)))
   (vertices rel)))

(defn terminal-common-successors?
  [rel]

  (every?
   (fn [i]
     (or
      (not (<= (proper-out-degree rel i) 2))
      (= (proper-in-degree rel i) 0)))
   (vertices rel)))

; Subclass closed families of infinite rank
(defn acyclic-relation?
  [rel]

  (and
   (binary-relation? rel)
   (every? singular-universal? (strong-connectivity rel))))

; Moore families of rank two
(def reflexive-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set (map (fn [pair] (list (first pair) (first pair))) rel))))))

(def reflexive-successors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set (map (fn [pair] (list (second pair) (second pair))) rel))))))

(def reflexive?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set (map (fn [i] (list i i)) (vertices rel)))))))

(def symmetric-binary-relation?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      (set rel)
      (set (map reverse rel))))))

(def dependency-relation?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set (map reverse rel))
      (set (map (fn [i] (list i i)) (apply union (map set rel))))))))

; Moore families of rank three
(def reflexive-loop-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y] (cartesian-product coll coll)
               :when (and (not= x y)
                          (rel (list x y))
                          (rel (list y y)))]
           (list x x))))))))

(def reflexive-loop-successors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y] (cartesian-product coll coll)
               :when (and (not= x y)
                          (rel (list x y))
                          (rel (list x x)))]
           (list y y))))))))

(def reflexive-symmetric-component?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y] (cartesian-product coll coll)
               :when (and (not= x y)
                          (rel (list x y))
                          (rel (list y x)))]
           #{(list x x) (list y y)})))))))

(def reflexive-far-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x y))
                      (rel (list y z)))]
           (list x x))))))))

(def reflexive-center?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x y))
                      (rel (list y z)))]
           (list y y))))))))

(def reflexive-far-sucessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x y))
                      (rel (list y z)))]
           (list z z))))))))

(def reflexive-multiple-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x z))
                      (rel (list y z)))]
           #{(list x x) (list y y)})))))))

(def reflexive-multiple-successors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x y))
                      (rel (list x z)))]
           #{(list y y) (list z z)})))))))

(def reflexive-common-successors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x z))
                      (rel (list y z)))]
           (list z z))))))))

(def reflexive-common-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (apply distinct? (list x y z))
                      (rel (list x y))
                      (rel (list x z)))]
           (list x x))))))))

; Symmetric related moore families
(def symmetric-loop-origin?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y] (cartesian-product coll coll)
               :when (and (not= x y)
                          (rel (list x x))
                          (rel (list x y)))]
           (list y y))))))))

(def symmetric-loop-target?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y] (cartesian-product coll coll)
               :when (and (not= x y)
                          (rel (list y y))
                          (rel (list x y)))]
           (list x x))))))))

(def symmetric-common-edge-origin?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (not= x y)
                          (not= x z)
                          (not= y z)
                          (rel (list x y))
                          (rel (list x z)))]
           #{(list y x) (list z x)})))))))

(def symmetric-common-edge-target?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (not= x y)
                          (not= x z)
                          (not= y z)
                          (rel (list x z))
                          (rel (list y z)))]
           #{(list z x) (list z y)})))))))

(def symmetric-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (not= x y)
                      (not= x z)
                      (not= y z)
                      (rel (list x y))
                      (rel (list y z)))]
           (list y x))))))))

(def symmetric-successors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and
                      (not= x y)
                      (not= x z)
                      (not= y z)
                      (rel (list x y))
                      (rel (list y z)))]
           (list z y))))))))

; Complete common endpoints
(def complete-common-predecessors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (not= x y)
                          (not= x z)
                          (not= y z)
                          (rel (list x z))
                          (rel (list y z)))]
           #{(list x y) (list y x)})))))))

(def complete-common-successors?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (not= x y)
                          (not= x z)
                          (not= y z)
                          (rel (list x y))
                          (rel (list x z)))]
           #{(list y z) (list z y)})))))))

(def left-euclidean?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (rel (list x z)) (rel (list y z)))]
           (list x y))))))))

(def right-euclidean?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (rel (list x y)) (rel (list x z)))]
           (list y z))))))))

; Circular relations
(def edge-circular?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (apply distinct? (list x y z)) (rel (list x y)) (rel (list y z)))]
           (list z x))))))))

(def circular-relation?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (set
       (let [coll (vertices rel)]
         (for [[x y z] (cartesian-product coll coll coll)
               :when (and (rel (list x y)) (rel (list y z)))]
           (list z x))))))))

; Transitive relations
(def edge-transitive?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      rel
      (apply
       union
       (set
        (map
         (fn [i]
           (set
            (map
             (fn [j]
               (list j i))
             (difference (predecessors rel i) #{i}))))
         (vertices rel))))))))

(def transitive?
  (moore-family
   size-two-seq?
   (letfn [(get-immediate-targets [rel vertex]
             (set
              (for [ordered-pair rel
                    :when (and
                           (size-two-seq? ordered-pair)
                           (= (first ordered-pair) vertex))]
                (second ordered-pair))))
           (get-targets [rel added to-add]
             (if (superset? (list to-add added))
               added
               (get-targets
                rel
                (union added to-add)
                (apply union (map (partial get-immediate-targets rel) to-add)))))
           (reachable-from [rel vertex]
             (get-targets rel #{} (get-immediate-targets rel vertex)))]
     (fn [rel]
       (apply
        union
        (map
         (fn [i]
           (set
            (map
             (fn [j]
               (list i j))
             (reachable-from rel i))))
         (vertices rel)))))))

(def preorder?
  (moore-family
   size-two-seq?
   (fn [rel]
     (union
      (set (map (fn [i] (list i i)) (vertices rel)))
      (cl transitive? rel)))))

; Symmetric binary relations
(defn symmetric-binary-relation
  [coll]

  (if (set? coll)
    (apply
     union
     (map
      (fn [edge]
        (if (= (count edge) 1)
          #{(list (first edge) (first edge))}
          (let [ordered-edge (seq edge)]
            #{ordered-edge (reverse ordered-edge)})))
      coll))
    (assoc (Universal.
            (fn [pair]
              (and
               (size-two-seq? pair)
               (coll (set pair)))))
      :arities #{2})))

(defn symmetric-component
  [rel]

  (intersection rel (transpose rel)))

(defn complement-binary-relation
  [rel]

  (clojure.set/difference (complete-relation (vertices rel)) rel))

(defn relation-orientations
  [rel]

  (let [reflexive-elements (set
                            (filter
                             (fn [i]
                               (rel (list i i)))
                             (vertices rel)))
        unordered-pairs (set
                         (for [i rel
                               :when (apply distinct? i)]
                           (set i)))
        orientations (set
                      (map
                       (fn [pair]
                         (let [current-orientation (seq pair)]
                           #{current-orientation
                             (reverse current-orientation)}))
                       unordered-pairs))]
    (set
     (map
      (fn [edges]
        (union
         (coreflexive-relation reflexive-elements)
         (set edges)))
      (apply cartesian-product orientations)))))

(defn relation-dependencies
  [rel]

  (set (map set rel)))

; Classes of equivalence relations
(def equivalence-relation?
  (moore-family
    size-two-seq?
    (fn [rel]
      (equivalence-relation (weak-connectivity rel)))))

(def complete-relation?
  (assoc (Universal.
           (fn [coll]
             (or
               (= (type coll) CompleteRelation)
               (and
                 (= (type coll) BinaryCartesianProduct)
                 (= (relation-domain coll) (relation-codomain coll)))
               (and (binary-relation? coll)
                    (equal-universals? coll (complete-relation (vertices coll)))))))
    :closure (fn [rel]
               (complete-relation (vertices rel)))))

(def threshold-equivalence-relation?
  (moore-family
    size-two-seq?
    (fn [rel]
      (let [isolated-elements (apply
                                union
                                (intersection
                                  singular-universal?
                                  (weak-connectivity rel)))]
        (equivalence-relation
          (union
            (set (map (fn [i] #{i}) isolated-elements))
            #{(clojure.set/difference (vertices rel) isolated-elements)}))))))

(defn regular-equivalence-relation?
  [rel]

  (and
    (equivalence-relation? rel)
    (let [coll (weak-connectivity rel)]
      (equal-seq? (map count coll)))))

(defn two-regular-equivalence-relation?
  [rel]

  (and
    (equivalence-relation? rel)
    (let [coll (weak-connectivity rel)]
      (every?
        (fn [i]
          (= (count i) 2))
        coll))))

(defn three-regular-equivalence-relation?
  [rel]

  (and
    (equivalence-relation? rel)
    (let [coll (weak-connectivity rel)]
      (every?
        (fn [i]
          (= (count i) 3))
        coll))))

(defn four-regular-equivalence-relation?
  [rel]

  (and
    (equivalence-relation? rel)
    (let [coll (weak-connectivity rel)]
      (every?
        (fn [i]
          (= (count i) 4))
        coll))))

; Classes of symmetric binary relations
(def independency-relation?
  (moore-family
   distinct-size-two-seq?
   (fn [rel]
     (union
      rel
      (set (map reverse rel))))))

(defn perfect-relation?
  [rel]

  (letfn [(hole? [current-rel]
            (every?
             (fn [i]
               (= 2 (count (query current-rel {0 i}))))
             (vertices current-rel)))
          (odd-hole-free? [current-rel]
            (every?
             (fn [i]
               (and
                (odd? i)
                (every?
                 (fn [current-coll]
                   (not (hole? (subrelation rel current-coll))))
                 (selections (vertices rel) i))))
             (range 5 (inc (count (vertices current-rel))))))]
    (and
     (symmetric-binary-relation? rel)
     (odd-hole-free? rel)
     (odd-hole-free?
      (union
       (coreflexive-relation (vertices rel))
       (complement-binary-relation rel))))))

(def comparability-relation?
  (intersection
   symmetric-binary-relation?
   (fn [rel]
     (let [orientations (relation-orientations rel)]
       (not
        (every?
         (complement
          (fn [rel]
            (let [coll (vertices rel)]
              (every?
               (fn [[a b c]]
                 (if (and (rel (list a b))
                          (rel (list b c)))
                   (rel (list a c))
                   true))
               (cartesian-product coll coll coll)))))
         orientations))))))

(def incomparability-relation?
  (comp comparability-relation? complement-binary-relation))

(def permutation-symmetric-relation?
  (intersection
   comparability-relation?
   incomparability-relation?))

(defn chordal-relation?
  [rel]

  (letfn [(hole? [current-rel]
            (every?
             (fn [i]
               (= 2 (count (query current-rel {0 i}))))
             (vertices current-rel)))]
    (and
     (symmetric-binary-relation? rel)
     (every?
      (fn [coll]
        (or
         (<= (count coll) 3)
         (not (hole? (subrelation rel coll)))))
      (power-set (vertices rel))))))

(def cochordal-relation?
  (comp chordal-relation? complement-binary-relation))

(def split-relation?
  (intersection
   chordal-relation?
   cochordal-relation?))

(def split-permutation-relation?
  (intersection
   permutation-relation?
   chordal-relation?
   cochordal-relation?))

(def complement-reducible-relation?
  (partial
   every-component?
   (fn [component]
     (let [complement-components (weakly-connected-components
                                  (complement-binary-relation
                                   component))]
       (if (= 1 (count complement-components))
         (= 1 (count (vertices component)))
         (every?
          complement-reducible-relation?
          complement-components))))))

(def trivially-perfect-relation?
  (partial
   every-component?
   (fn [component]
     (letfn [(total-element? [rel elem]
               (every?
                (fn [i]
                  (and
                   (rel (list i elem))
                   (rel (list elem i))))
                (vertices rel)))]
       (let [total-elements (set
                             (filter
                              (partial total-element? component)
                              (vertices component)))]
         (and
          (not (empty? total-elements))
          (trivially-perfect-relation?
           (subrelation
            component
            (clojure.set/difference
             (vertices component)
             total-elements)))))))))

(defn cotrivially-perfect-relation?
  [rel]

  (trivially-perfect-relation?
   (union
    (coreflexive-relation (vertices rel))
    (complement-binary-relation rel))))

(defn complete-multipartite-relation?
  [rel]

  (and
   (dependency-relation? rel)
   (equivalence-relation?
    (union
     (coreflexive-relation (vertices rel))
     (complement-binary-relation rel)))))

(defn threshold-relation?
  [rel]

  (letfn [(total-element? [rel elem]
            (every?
             (fn [i]
               (and
                (rel (list i elem))
                (rel (list elem i))))
             (vertices rel)))
          (isolated-element? [rel elem]
            (every?
             (fn [i]
               (and
                (not (rel (list i elem)))
                (not (rel (list elem i)))))
             (clojure.set/difference (vertices rel) #{elem})))
          (acquire-elements [pred? rel]
            (set
             (filter
              (partial pred? rel)
              (vertices rel))))
          (remove-elements [rel coll]
            (subrelation
             rel
             (clojure.set/difference (vertices rel) coll)))]
    (let [isolated-elements (acquire-elements isolated-element? rel)]
      (if (empty? isolated-elements)
        (let [total-elements (acquire-elements total-element? rel)]
          (if (empty? total-elements)
            (empty? rel)
            (threshold-relation? (remove-elements rel total-elements))))
        (threshold-relation? (remove-elements rel isolated-elements))))))

; Anticoreflexive
(def anticoreflexive?
  (intersection
   binary-relation?
   (fn [rel]
     (every?
      (fn [[a b]]
        (or
         (= a b)
         (rel (list a b))
         (rel (list b a))))
      (cartesian-power (vertices rel) 2)))))

; Ouput sets and input sets
(defn output-sets
  [order]

  (multiset
   (map
    (fn [i]
      (query order {0 i}))
    (vertices order))))

(defn input-sets
  [order]

  (multiset
   (map
    (fn [i]
      (query order {1 i}))
    (vertices order))))

(defn distinct-output-sets
  [order]

  (set
   (map
    (fn [i]
      (query order {0 i}))
    (vertices order))))

(defn distinct-input-sets
  [order]

  (set
   (map
    (fn [i]
      (query order {1 i}))
    (vertices order))))

; Covering and related functionality
(defn covers?
  [rel a b]

  (and
   (rel (list a b))
   (= (count
       (intersection
        (query rel {0 a})
        (query rel {1 b})))
      2)))

(defn covering-relation
  [rel]

  (let [proper-rel (set (filter distinct-size-two-seq? rel))
        composites (set
                     (for [[[a b] [c d]] (cartesian-power proper-rel 2)
                           :when (= b c)]
                       [a d]))]
    (difference proper-rel composites)))

; Supremum and infimum
(defn get-lower-bounds
  [rel elems]

  (set
   (filter
    (fn [elem]
      (every?
       (fn [i]
         (rel (list elem i)))
       elems))
    (vertices rel))))

(defn get-upper-bounds
  [rel elems]

  (set
   (filter
    (fn [elem]
      (every?
       (fn [i]
         (rel (list i elem)))
       elems))
    (vertices rel))))

(defn infimum
  [rel elems]

  (letfn [(maximal-elements [rel elems]
            (set
             (filter
              (fn [i]
                (every?
                 (complement
                  (fn [j]
                    (and
                     (not= i j)
                     (rel (list i j)))))
                 elems))
              elems)))]
    (maximal-elements rel (get-lower-bounds rel elems))))

(defn supremum
  [rel elems]

  (letfn [(minimal-elements [rel elems]
            (set
             (filter
              (fn [i]
                (every?
                 (complement
                  (fn [j]
                    (and
                     (not= i j)
                     (rel (list j i)))))
                 elems))
              elems)))]
    (minimal-elements rel (get-upper-bounds rel elems))))

; Order theoretic functionality
(defn preceding-set?
  [rel coll1 coll2]

  (and
   (every?
    (fn [i]
      (every?
       (fn [j]
         (rel (list i j)))
       coll2))
    coll1)
   (every?
    (fn [i]
      (every?
       (fn [j]
         (not (rel (list i j))))
       coll1))
    coll2)))

(defn child-weak-order
  [rel]

  (letfn [(preceding-lower-set? [rel coll]
            (preceding-set?
             rel
             coll
             (clojure.set/difference
              (vertices rel)
              coll)))
          (acquire-lower-set [rel n]
            (if (= n (count (vertices rel)))
              (vertices rel)
              (let [current-lower-sets (filter
                                        (partial preceding-lower-set? rel)
                                        (selections (vertices rel) n))]
                (if (empty? current-lower-sets)
                  (acquire-lower-set rel (inc n))
                  (first current-lower-sets)))))]
    (if (empty? (vertices rel))
      []
      (let [coll (acquire-lower-set rel 1)]
        (vec
         (cons
          coll
          (child-weak-order
           (subrelation
            rel
            (clojure.set/difference
             (vertices rel)
             coll)))))))))

(defn ordinal-decomposition
  [rel]

  (vec
   (map
    (partial subrelation rel)
    (child-weak-order rel))))

(defn order-height
  [rel]

  (apply
   max
   (for [i (power-set (vertices rel))
         :when (complete-relation? (cl symmetric-binary-relation? (subrelation rel i)))]
     (count i))))

(defn predecessors-ordering
  [order]

  (let [coll (set
              (map
               (fn [i]
                 (let [v (query order {1 i})]
                   (clojure.set/difference v #{i})))
               (vertices order)))]
    (intersection
      superset?
      (cartesian-product coll coll))))

; Rankings
(defn lower-first-ranking
  [rel]

  (if (empty? rel)
    '()
    (let [current-minima (minimal-vertices rel)]
      (cons
        current-minima
        (lower-first-ranking (subrelation rel (difference (vertices rel) current-minima)))))))

(defn upper-first-ranking
  [rel]

  (if (empty? rel)
    '()
    (let [current-maxima (maximal-vertices rel)]
      (cons
        current-maxima
        (lower-first-ranking (subrelation rel (difference (vertices rel) current-maxima)))))))

; Lattice related functionality
(defn monoidalize
  "This turns a function into a monoid."
  ([func]
     (fn
       ([a] a)
       ([a b] (func a b))
       ([a b & more] (reduce func (func a b) more))))
  ([func identity-element]
     (fn
       ([] identity-element)
       ([a] a)
       ([a b] (func a b))
       ([a b & more] (reduce func (func a b) more)))))

(defn join-irreducibles
  [order]

  (clojure.set/difference
   (vertices order)
   (apply
    union
    (map
     (fn [coll]
       (let [suprema (supremum order coll)]
         (if (and (singular-universal? suprema)
                  (not (superset? (list suprema coll))))
           suprema
           #{})))
     (power-set (vertices order))))))

(defn meet-operation
  [rel]

  (monoidalize
   (fn [a b]
     (first
      (infimum
       rel
       (set (list a b)))))))

(defn join-operation
  [rel]

  (monoidalize
   (fn [a b]
     (first
      (supremum
       rel
       (set (list a b)))))))

(defn modularity-relation
  [rel]

  (let [join (join-operation rel)
        meet (meet-operation rel)]
    (intersection
     (fn [[a b]]
       (every?
        (fn [x]
          (or
           (not (and (rel (list (meet a b) x))
                     (rel (list x b))))
           (= x (meet (join x a) b))))
        (vertices rel)))
     (cartesian-product (vertices rel) (vertices rel)))))

(defn complementation-relation
  [rel]

  (let [join (join-operation rel)
        meet (meet-operation rel)]
    (intersection
     (fn [[a b]]
       (let [current-meet (meet a b)
             current-join (join a b)]
         (and
          (every?
           (fn [vertex]
             (rel (list current-meet vertex)))
           (vertices rel))
          (every?
           (fn [vertex]
             (rel (list vertex current-join)))
           (vertices rel)))))
     (cartesian-product (vertices rel) (vertices rel)))))

; Principal ideals and principal filters
(defn principal-ideal
  [rel elem]

  (intersection
   rel
   (let [coll (query rel {1 elem})]
     (cartesian-product coll coll))))

(defn principal-filter
  [rel elem]

  (intersection
   rel
   (let [coll (direct-successors rel elem)]
     (cartesian-product coll coll))))

(defn order-suborders
  [order]

  (letfn [(suborder-parts [order coll]  
            (map
             (partial apply union)
             (apply
              cartesian-product
              (map
               (fn [i]
                 (union
                  #{#{}}
                  (set
                   (map
                    (fn [i] #{i})
                    (query order {1 i})))))
               coll))))]
    (let [coll (power-set (vertices order))]
      (apply
       union
       (map
        (fn [i]
          (set
           (map
            (fn [j]
              (list j i))
            (suborder-parts order i))))
        coll)))))

; Methods of creating new preorders
(defn logical-preorder
  [func coll]

  (intersection
   (fn [[a b]]
     (superset? (list (func a) (func b))))
   (cartesian-product coll coll)))

(defn specialization-preorder
  [coll]

  (if (set? coll)
    (logical-preorder
     (fn [i]
       (cl coll #{i}))
     (apply union coll))
    (assoc (Universal.
             (fn [[a b]]
              (superset? (list (cl coll #{a}) (cl coll #{b})))))
      :arities #{2})))

(defn domain-preorder
  [rel]

  (logical-preorder
    (fn [vertex]
      (direct-successors rel vertex))
    (vertices rel)))

(defn codomain-preorder
  [rel]

  (logical-preorder
    (fn [vertex]
      (direct-predecessors rel vertex))
    (vertices rel)))

; Partial orders defined by forbidden suborders
(def partial-order?
  (intersection
   antisymmetric?
   transitive?
   reflexive?))

(def total-order?
  (intersection
   partial-order?
   anticoreflexive?))

(def height-two-order?
  (intersection
   height-two?
   partial-order?))

(def lower-forest?
  (intersection
   partial-order?
   (fn [rel]
     (let [coll (vertices rel)]
       (every?
        (complement
         (fn [[a b c]]
           (and
            (distinct? a b c)
            (not (rel (list a b)))
            (not (rel (list b a)))
            (rel (list a c))
            (rel (list b c)))))
        (cartesian-product coll coll coll))))))

(def upper-forest?
  (intersection
   partial-order?
   (fn [rel]
     (let [coll (vertices rel)]
       (every?
        (complement
         (fn [[a b c]]
           (and
            (distinct? a b c)
            (not (rel (list b c)))
            (not (rel (list c b)))
            (rel (list a b))
            (rel (list a c)))))
        (cartesian-product coll coll coll))))))

(def weak-order?
  (intersection
   partial-order?
   (comp (partial every? coreflexive?) ordinal-decomposition)))

(comment
  (def width-two-order?
           (intersection
            partial-order?
            (fn [rel] (<= (independence-number (set (map set rel))) 2)))))

(def set-of-lists?
  (partial every-component? total-order?))

(def height-two-lower-forest?
  (intersection
   lower-forest?
   height-two-order?))

(def height-two-upper-forest?
  (intersection
   upper-forest?
   height-two-order?))

(def height-two-set-of-lists?
  (intersection
   set-of-lists?
   height-two-order?))

(defn set-of-ordered-pairs?
  [rel]

  (and
    (set-of-lists? rel)
    (every?
      (fn [i]
        (= (count i) 2))
      (weak-connectivity rel))))

(defn set-of-ordered-triples?
  [rel]

  (and
    (set-of-lists? rel)
    (every?
      (fn [i]
        (= (count i) 3))
      (weak-connectivity rel))))

(defn set-of-ordered-quadruples?
  [rel]

  (and
    (set-of-lists? rel)
    (every?
      (fn [i]
        (= (count i) 4))
      (weak-connectivity rel))))

(def strongly-unique-extrema-order?
  (intersection
   partial-order?
   (fn [rel]
     (let [coll (vertices rel)]
       (every?
        (fn [[a b c d]]
          (not
           (and
            (rel (list a c))
            (rel (list a d))
            (rel (list b c))
            (rel (list b d))
            (not (rel (list a b)))
            (not (rel (list c d))))))
        (cartesian-product coll coll coll coll))))))

(def series-parallel-order?
  (partial
   every-component?
   (fn [component]
     (if (<= (count component) 3)
       (partial-order? component)
       (and
        (partial-order? component)
        (let [ordinal-elems (ordinal-decomposition component)]
          (every?
           (fn [ordinal-elem]
             (and
              (or (= (count (vertices ordinal-elem)) 1)
                  (< 1 (count (weak-connectivity ordinal-elem))))
              (series-parallel-order? ordinal-elem)))
           ordinal-elems)))))))

(def interval-order?
  (comp total-order? predecessors-ordering))

(def diamond-free-order?
  (partial
   every-component?
   (fn [component]
     (if (<= (count component) 3)
       (partial-order? component)
       (every?
        (fn [coll]
          (not=
           (list 1 2 1)
           (map count (child-weak-order (subrelation component coll)))))
        (selections (vertices component) 4))))))

(def strongly-unique-extrema-interval-order?
  (intersection
   strongly-unique-extrema-order?
   interval-order?))

(def semiorder?
  (intersection
   partial-order?
   (fn [order]
     (every?
      (fn [coll]
        (let [component (subrelation order coll)]
          (or
           (not= (count (weak-connectivity component)) 1)
           (not (set-of-lists? component)))))
      (selections (vertices order) 4)))))

(def series-parallel-interval-order?
  (intersection
   series-parallel-order?
   interval-order?))

(def series-parallel-semiorder?
  (intersection
   series-parallel-order?
   semiorder?))

(def multitree?
  (partial
   every-component?
   (intersection
    partial-order?
    (fn [rel]
      (let [coll (vertices rel)]
        (or
         (<= (count coll) 3)
         (every?
          (complement
           (fn [[a b c d]]
             (and
              (rel (list a d))
              (rel (list b c))
              (rel (list b d))
              (not (rel (list a b)))
              (not (rel (list b a)))
              (not (rel (list c d)))
              (not (rel (list d c))))))
          (cartesian-product coll coll coll coll))))))))

(def diamond-free-multitree?
  (intersection
   diamond-free-order?
   multitree?))

(def height-two-strongly-unique-extrema-order?
  (intersection
   height-two-order?
   strongly-unique-extrema-order?))

(def common-point-free-order?
  (intersection
   partial-order?
   (fn [rel]
     (let [all-elements (vertices rel)]
       (every?
        (fn [i]
          (let [coll (disj all-elements i)]
            (or
             (every?
              (complement
               (fn [[a b]]
                 (and
                  (rel (list a i))
                  (rel (list b i)))))
              (cartesian-product coll coll))
             (every?
              (complement
               (fn [[c d]]
                 (and
                  (rel (list i c))
                  (rel (list i d)))))
              (cartesian-product coll coll)))))
        all-elements)))))

(def weak-interval-order?
  (comp weak-order? predecessors-ordering))

; Uniquely connected orders
(defn uniquely-connected-order?
  [rel]

  (and
   (partial-order? rel)
   (<= (count (weak-connectivity rel)) 1)))

(defn unique-minima-order?
  [order]

  (and
   (partial-order? order)
   (<= (count (supremum order #{})) 1)))

(defn unique-maxima-order?
  [order]

  (and
   (partial-order? order)
   (<= (count (infimum order #{})) 1)))

(defn uniquely-bounded-order?
  [order]

  (and
   (partial-order? order)
   (<= (count (infimum order #{})) 1)
   (<= (count (supremum order #{})) 1)))

(defn lower-bounded-order?
  [order]

  (and
   (partial-order? order)
   (singular-universal? (supremum order #{}))))

(defn upper-bounded-order?
  [order]

  (and
   (partial-order? order)
   (singular-universal? (infimum order #{}))))

(defn bounded-order?
  [order]

  (and
   (partial-order? order)
   (singular-universal? (supremum order #{}))
   (singular-universal? (infimum order #{}))))

; Specific uniquely connected orders
(def lower-tree?
  (intersection
   lower-forest?
   (fn [rel]
     (<= (count (supremum rel #{})) 1))))

(def upper-tree?
  (intersection
   upper-forest?
   (fn [rel]
     (<= (count (infimum rel #{})) 1))))

(def uniquely-connected-height-two-order?
  (intersection
   uniquely-connected-order?
   height-two-order?))

(def height-two-lower-tree?
  (intersection
   lower-tree?
   height-two-order?))

(def height-two-upper-tree?
  (intersection
   upper-tree?
   height-two-order?))

; Unique extrema orders
(defn unique-extrema?
  [order]
  
  (and
   (partial-order? order)
   (every?
    (fn [[x y]]
      (and
       (<= (count (infimum order (list x y))) 1)
       (<= (count (supremum order (list x y))) 1)))
    (cartesian-product
     (vertices order)
     (vertices order)))))

(defn atomistic-order?
  [order]

  (every?
   (fn [i]
     (<= (count (query order {1 i})) 2))
   (join-irreducibles order)))

(def lower-rooted-tree?
  (intersection
    lower-bounded-order?
    lower-forest?))

(def upper-rooted-tree?
  (intersection
    upper-bounded-order?
    upper-forest?))

(defn lattice-relation?
  [order]
  
  (and
   (partial-order? order)
   (every?
    (fn [coll]
      (= 1
         (count (supremum order coll))
         (count (infimum order coll))))
    (selections (vertices order) 2))))

(def atomistic-lattice-relation?
  (intersection
    lattice-relation?
    atomistic-order?))

(def m-symmetric-lattice-relation?
  (intersection
    lattice-relation?
    (fn [order]
     (let [rel (modularity-relation order)]
       (= rel (union rel (transpose rel)))))))

(def modular-lattice-relation?
  (intersection
    lattice-relation?
    (fn [order]
     (complete-relation? (cl symmetric-binary-relation? (modularity-relation order))))))

(def distributive-lattice-relation?
  (intersection
    lattice-relation?
    (fn [order]
     (let [coll (vertices order)
           join (join-operation order)
           meet (meet-operation order)]
       (every?
        (fn [[x y z]]
          (= (meet x (join y z))
             (join
              (meet x y)
              (meet x z))))
        (cartesian-product coll coll coll))))))

(def complemented-lattice-relation?
  (intersection
    lattice-relation?
    (complement empty?)
    (fn [rel]
     (let [comrel (complementation-relation rel)]
       (= (vertices rel) (vertices comrel))))))

(def uniquely-complemented-lattice-relation?
  (intersection
    lattice-relation?
    (complement empty?)
    (fn [rel]
     (let [comrel (complementation-relation rel)]
       (every?
        (fn [i]
          (= (count (query comrel {0 i})) 1))
        (vertices rel))))))

(def boolean-algebra-relation?
  (intersection
    distributive-lattice-relation?
    (complement empty?)
    (fn [rel]
     (let [comrel (complementation-relation rel)]
       (every?
        (fn [i]
          (= (count (query comrel {0 i})) 1))
        (vertices rel))))))

; Methods of creating new preorders
(def total-preorder?
  (intersection
   preorder?
   anticoreflexive?))

(def weak-preorder?
  (intersection
   reflexive?
   (comp (partial every? equivalence-relation?) ordinal-decomposition)))

(defn series-parallel-preorder?
  [rel]

  (and
   (preorder? rel)
   (series-parallel-order? (condensation rel))))

; Uniquely connected preorders
(defn uniquely-connected-preorder?
  [rel]

  (and
   (partial-order? rel)
   (<= (count (weak-connectivity rel)) 1)))

(defn lower-bounded-preorder?
  [rel]

  (and
   (preorder? rel)
   (singular-universal? (supremum rel #{}))))

(defn upper-bounded-preorder?
  [rel]

  (and
   (preorder? rel)
   (singular-universal? (infimum rel #{}))))

(defn bounded-preorder?
  [rel]

  (and
   (preorder? rel)
   (singular-universal? (supremum rel #{}))
   (singular-universal? (infimum rel #{}))))

; Strict orders
(def strict-order?
  (intersection
   irreflexive?
   transitive?))

(def strict-total-order?
  (intersection
    strict-order?
    anticoreflexive?))

(def strict-set-of-lists?
  (partial every-component? strict-total-order?))

(defn strict-weak-order?
  [rel]

  (and
    (strict-order? rel)
    (weak-order? (cl reflexive? rel))))

; A component size regular relation is a binary relation such that
; each connected component in the relation is of the same size
(defn weak-component-size-regular-relation?
  [rel]

  (and
    (binary-relation? rel)
    (equal-seq? (map count (weak-connectivity rel)))))

(defn strong-component-size-regular-relation?
  [rel]

  (and
    (binary-relation? rel)
    (equal-seq? (map count (weak-connectivity rel)))))

; Additional classes of relations
(def trichotomous?
  (intersection   
   asymmetric?
   anticoreflexive?))

(defn covering-relation?
  [rel]

  (and
   (irreflexive? rel)
   (acyclic-relation? rel)
   (every?
    (fn [[a b]]
      (not
       (and (= (second a) (first b))
            (rel (list (first a) (second b))))))
    (cartesian-product rel rel))))

(defn symmetric-strongly-connected-components?
  [rel]

  (every?
   (fn [component]
     (let [component-rel (subrelation rel component)]
       (symmetric-binary-relation? component-rel)))
   (strong-connectivity rel)))

(defn complete-strongly-connected-components?
  [rel]

  (every?
   (fn [component]
     (let [component-relation (subrelation rel component)]
       (and (symmetric-binary-relation? component-relation)
            (complete-relation? (cl reflexive? component-relation)))))
   (strong-connectivity rel)))

(def left-total?
  (intersection
   binary-relation?
   (fn [rel] (total-on? rel #{0}))))

(def right-total?
  (intersection
   binary-relation?
   (fn [rel] (total-on? rel #{1}))))

(def bitotal?
  (intersection
   binary-relation?
   (fn [rel] (total-on? rel #{0}))
   (fn [rel] (total-on? rel #{1}))))

(def total-relation?
  (intersection
   reflexive?
   anticoreflexive?))

; Test for strong and weak connectivity
(defn strongly-connected-relation?
  [rel]

  (and
    (binary-relation? rel)
    (= (count (strong-connectivity rel)) 1)))

(defn weakly-connected-relation?
  [rel]

  (and
    (binary-relation? rel)
    (= (count (weak-connectivity rel)) 1)))

(def connected-partial-order?
  (intersection
    partial-order?
    weakly-connected-relation?))

(def connected-symmetric-relation?
  (intersection
    symmetric-binary-relation?
    weakly-connected-relation?))

(def connected-dependency-relation?
  (intersection
    dependency-relation?
    weakly-connected-relation?))

; Cartesian product relations
(def cartesian-product?
  (assoc (Universal.
          (fn [coll]
            (or
             (= (type coll) CompleteRelation)
             (= (type coll) BinaryCartesianProduct)
             (and (binary-relation? coll)
                  (equal-universals? coll (cartesian-product (relation-domain coll)
                                                             (relation-codomain coll)))))))
         :closure (fn [rel]
                    (cartesian-product (relation-domain rel)
                                       (relation-codomain rel)))))