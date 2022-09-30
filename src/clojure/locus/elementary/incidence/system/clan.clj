(ns locus.elementary.incidence.system.clan
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all])
  (:import [locus.base.logic.core.set Multiset]))

; A set of multisets has been called by a number of different names in the literature such as "macroset."
; We will be doing a lot of work with multiset systems, so convenience sake we will call them clans.

; Clan builder
(defn clan
  [coll]

  (set (map multiset coll)))

; Clan visualizer
(defn clan-covering
  [family]

  (mapcat
   (fn [i]
     (let [n (count i)]
       (for [pred family
             :let [pred-size (count pred)]
             :when (and (< pred-size n)
                        (superbag? (list pred i))
                        (every?
                         (fn [middle]
                           (not
                            (and (not= middle i)
                                 (not= middle pred)
                                 (superbag? (list pred middle))
                                 (superbag? (list middle i)))))
                         family))]
         (list pred i))))
   family))

; Clan reductions
(defn clan-reductions
  [coll]

  (conj
   (set
    (map
     set
     (apply
      cartesian-product
      (set
       (map
        power-clan
        coll)))))
   #{}))

(defn nullfree-clan-reductions
  [coll]

  (set
   (map
    (fn [i]
      (set (filter (fn [elem] (not= 0 (count elem))) i)))
    (clan-reductions coll))))

; Convert clan
(defn convert-clan
  "Convert a clan into a set system"
  [coll]

  (letfn [(multiset-to-set [arg]
            (apply
             union
             (map
              (fn [key]
                (set
                 (map
                  (fn [i]
                    (list key i))
                  (range 1 (inc (multiplicity arg key))))))
              (support arg))))]
    (set (map multiset-to-set coll))))

; Clans
(defn clan?
  [coll]

  (and
   (universal? coll)
   (every? multiset? coll)))

; Cardinality classification
; Classification of clans by their internal properties
(def singular-clan?
  (intersection
   clan?
   singular-universal?))

(def size-two-clan?
  (intersection
   clan?
   size-two-universal?))

(def size-three-clan?
  (intersection
   clan?
   size-three-universal?))

(def size-four-clan?
  (intersection
   clan?
   size-four-universal?))

(defn unique-clan?
  [coll]

  (and
   (clan? coll)
   (unique-universal? coll)))

(def max-size-two-clan?
  (intersection
   max-size-two-universal?
   clan?))

(def max-size-three-clan?
  (intersection
   max-size-three-universal?
   clan?))

(def max-size-four-clan?
  (intersection
   max-size-four-universal?
   clan?))

; Classification of clans by their member properties
(defn rank-two-clan?
  [coll]

  (every? max-size-two-multiset? coll))

(defn rank-three-clan?
  [coll]

  (every? max-size-three-multiset? coll))

(defn rank-four-clan?
  [coll]

  (every? max-size-four-multiset? coll))

(defn nullfree-clan?
  [coll]

  (and
   (clan? coll)
   (every? (fn [i] (<= 1 (count i))) coll)))

(def nullfree-rank-two-clan?
  (intersection
   nullfree-clan?
   rank-two-clan?))

(def nullfree-rank-three-clan?
  (intersection
   nullfree-clan?
   rank-three-clan?))

(def nullfree-rank-four-clan?
  (intersection
   nullfree-clan?
   rank-four-clan?))

(def binary-clan?
  (power-set size-two-multiset?))

(def coreflexive-binary-clan?
  (power-set size-two-equal-multiset?))

(def ternary-clan?
  (power-set size-three-multiset?))

(def quaternary-clan?
  (power-set size-four-multiset?))

; Classification of clans by degrees
(defn regular-clan?
  [clan]

  (and
    (clan? clan)
    (let [degree-sequence (map (partial degree clan) (apply union (map set clan)))]
      (or (empty? degree-sequence) (apply = degree-sequence)))))

(defn two-regular-clan?
  [clan]

  (and
    (clan? clan)
    (every?
      (fn [i]
        (= (degree clan i) 2))
      (apply union (map set clan)))))

(defn three-regular-clan?
  [clan]

  (and
    (clan? clan)
    (every?
      (fn [i]
        (= (degree clan i) 3))
      (apply union (map set clan)))))

(defn four-regular-clan?
  [clan]

  (and
    (clan? clan)
    (every?
      (fn [i]
        (= (degree clan i) 3))
      (apply union (map set clan)))))

; Maximum degrees
(defn maximum-degree-two-clan?
  [clan]

  (and
    (clan? clan)
    (every?
      (fn [i]
        (<= (degree clan i) 2))
      (apply union (map set clan)))))

(defn maximum-degree-three-clan?
  [clan]

  (and
    (clan? clan)
    (every?
      (fn [i]
        (<= (degree clan i) 3))
      (apply union (map set clan)))))

(defn maximum-degree-four-clan?
  [clan]

  (and
    (clan? clan)
    (every?
      (fn [i]
        (<= (degree clan i) 4))
      (apply union (map set clan)))))

; Order rank
(defn order-rank
  [coll]

  (if (empty? coll)
    0
    (apply max (map multiset-order coll))))

(def order-rank-one-clan?
  "The elements of these clans are neccessarily strictly equal."
  (power-set equal-multiset?))

(def order-rank-two-clan?
  "This include the kuratowski clans"
  (power-set max-order-two-multiset?))

(def order-rank-three-clan?
  (power-set max-order-three-multiset?))

(def order-rank-four-clan?
  (power-set max-order-four-multiset?))

; Repetitiveness
(defn family-of-near-universals?
  [coll]

  (and
   (clan? coll)
   (every? near-universal? coll)))

; Special classes of clans
; Order theories of distributive lattices
(defn chain-clan?
  [coll]

  (and
   (clan? coll)
   (every?
    (fn [pair]
      (contains? pair (apply meet pair)))
    (selections coll 2))))

(defn sperner-clan?
  [coll]

  (and
   (clan? coll)
   (every?
    (fn [pair]
      (not (contains? pair (apply meet pair))))
    (selections coll 2))))

(def nullfree-chain-clan?
  (intersection
   nullfree-clan?
   chain-clan?))

(def nullfree-sperner-clan?
  (intersection
   nullfree-clan?
   sperner-clan?))

; Intersection related conditions
; Cardinalities of the results of lattice operations on subsets
(defn independent-clan?
  [coll]

  (and
   (clan? coll)
   (every?
    (fn [pair]
      (= (count (apply meet pair)) 0))
    (selections coll 2))))

(defn linear-clan?
  [coll]

  (and
   (clan? coll)
   (every? 
    (fn [pair]
      (<= (count (apply meet pair)) 1))
    (selections coll 2))))

(def partition-clan?
  (intersection
   nullfree-clan?
   independent-clan?))

; Laminar clan
(defn laminar-clan?
  [family]

  (every?
   (fn [pair]
     (let [[a b] (seq pair)]
       (or
        (empty? (apply intersection pair))
        (superbag? (list a b))
        (superbag? (list b a)))))
   (selections family 2)))

; Uniform clans
(defn uniform-clan?
  [coll]

  (and
   (clan? coll)
   (equal-seq? (map count coll))))

(defn cardinality-distinct-clan?
  [coll]

  (and
   (clan? coll)
   (or
    (= (count coll) 0)
    (distinct? (map count coll)))))

; Lets talk about the underlying multifamily instead now
(defn support-distinct-clan?
  [coll]

  (and
   (clan? coll)
   (or
    (= (count coll) 0)
    (distinct-seq? (map support coll)))))

(defn support-uniform-clan?
  [coll]

  (and
   (clan? coll)
   (or
    (= (count coll) 0)
    (apply = (map support coll)))))

; Order distinct clan
(defn order-distinct-clan?
  [coll]

  (and
   (clan? coll)
   (or
    (= (count coll) 0)
    (distinct? (map multiset-order coll)))))

(defn order-uniform-clan?
  [coll]

  (and
   (clan? coll)
   (or
    (= (count coll) 0)
    (apply = (map multiset-order coll)))))

; Signature uniform and distinct clans
(defn signature-uniform-clan?
  [coll]

  (and
   (clan? coll)
   (or (= (count coll) 0) (apply = (map signature coll)))))

(defn signature-distinct-clan?
  [coll]

  (and
   (clan? coll)
   (distinct-seq? (map signature coll))))

; Special balanced clans
(defn balanced-clan?
  [coll]

  (every?
   (fn [pair]
     (let [[a b] (seq pair)
           support-intersection (intersection (support a) (support b))]
       (every?
        (fn [i]
          (= (multiplicity a i)
             (multiplicity b i)))
        support-intersection)))
   (selections coll 2)))

; Maximum intersection order
(defn max-intersection-order-one-clan?
  [coll]

  (every?
   (fn [pair]
     (<= (multiset-order (apply meet pair)) 1))
   (selections coll 2)))

; Moore families associated with multisets
(def submultiset-closed?
  (moore-family
   multiset?
   (fn [coll]
     (apply union (map power-clan coll)))))

(def multiset-restriction-closed?
  (moore-family
   multiset?
   (fn [coll]
     (apply union (map multiset-restrictions coll)))))

(def subsingleton-closed-clan?
  (moore-family
   multiset?
   (fn [coll]
     (union
      coll
      (apply union (map (fn [i] (selections (support i) 1)) coll))))))

(def subnull-closed-clan?
  (moore-family
   multiset?
   (fn [coll]
     (if (empty? coll) coll (conj coll (multiset '()))))))

(def subuniversal-closed?
  (moore-family
   multiset?
   (fn [coll]
     (union
      coll
      (apply union (map (fn [i] (power-set (support i))) coll))))))

(def subequal-multiset-closed?
  (moore-family
   multiset?
   (fn [coll]
     (union
      coll
      (apply union (map equal-submultisets coll))))))

; Convex clans
(def convex-clan?
  (moore-family
   multiset?
   (fn [coll]
     (union
      coll
      (apply
       union
       (map
        (fn [[a b]]
          (if (not (superbag? (list a b)))
            #{}
            (interval-clan a b)))
        (cartesian-power coll 2)))))))

; Power clan
(def power-clan?
  (moore-family
   multiset?
   (fn [i]
     (power-clan (apply join i)))))

; Subsemilattices and sublattices of multisets
(def multiset-union-closed?
  (moore-family
   multiset?
   (fn [coll]
     (set
      (map
       (partial apply join)
       (disj (power-set coll) #{}))))))

(def multiset-intersection-closed?
  (moore-family
   multiset?
   (fn [coll]
     (set
      (map
       (partial apply meet)
       (disj (power-set coll) #{}))))))

(def multiset-extrema-closed?
  (moore-family
   multiset?
   (comp
    (partial cl multiset-intersection-closed?)
    (partial cl multiset-union-closed?))))

; Underlying degrees
(defn underlying-degree
  [coll i]

  (count
   (filter
    (fn [elem]
      (contains? (set elem) i))
    coll)))

(defn underlying-degrees
  [coll]

  (degrees (set (map set coll))))

; Constructor for binary clans
(defn clan-connectivity
  [coll]

  (family-connectivity (set (map set coll))))

(defn binary-clan
  [coll]

  (set
   (map
    (fn [i]
      (if (singular-universal? i)
        (Multiset. {(first i) 2})
        (multiset i)))
    coll)))

(def reflexive-binary-clan?
  (moore-family
   size-two-multiset?
   (fn [coll]
     (union
      coll
      (apply
       union
       (for [i coll
             :when (not (equal-multiset? i))
             :let [[a b] (seq i)]]
         #{(multiset (list a a))
           (multiset (list b b))}))))))

; Attempt to create a chain partition
(defn chain-partition
  [coll]

  (let [degrees-sequence (sort <= (set (vals (.multiplicities coll))))]
    (set
     (map
      (fn [current-degree]
        (set
         (filter
          (fn [i]
            (<= current-degree (multiplicity coll i)))
          (keys (.multiplicities coll)))))
      degrees-sequence))))

; Progression clans
(defn progression-clan
  [& coll]

  (set
   (map
    (fn [i]
      (multiset (take i coll)))
    (range 1 (inc (count coll))))))

(defn progression-clan?
  [coll]

  (letfn [(setify [coll]          
            (mapcat (fn [i] (map (fn [n] [i n]) (range (multiplicity coll i)))) (set coll)))]
    (and
     (clan? coll)
     (progression-family? (set (map (comp set setify) coll))))))

(def equal-progression-clan?
  (intersection
   progression-clan?
   order-rank-one-clan?))

(def size-two-progression-clan?
  (intersection
   progression-clan?
   size-two-clan?))

(def size-three-progression-clan?
  (intersection
   progression-clan?
   size-three-clan?))

(def size-four-progression-clan?
  (intersection
   progression-clan?
   size-four-clan?))

(def max-size-two-progression-clan?
  (intersection
   progression-clan?
   max-size-two-universal?))

(def max-size-three-progression-clan?
  (intersection
   progression-clan?
   max-size-three-universal?))

(def max-size-four-progression-clan?
  (intersection
   progression-clan?
   max-size-four-universal?))

; Balanced chain clans
(def balanced-chain-clan?
  (intersection
   balanced-clan?
   chain-clan?))

; Multiprogression clans
(defn multiprogression-clan?
  "These are like nullfree disjoint relations"
  [coll]

  
  (letfn [(setify [coll]          
            (mapcat
             (fn [i]
               (map
                (fn [n] [i n])
                (range (multiplicity coll i))))
             (set coll)))]
    (and
     (clan? coll)
     (multiprogression-family? (set (map (comp set setify) coll))))))

; Kuratowski clans
(defn parse-kuratowski-pair-multiset
  [coll]

  (if (= (count coll) 1)
    (list (first coll) (first coll))
    (let [all-elements (support coll)
          singular-elements (set
                             (filter
                              (fn [i]
                                (= (multiplicity coll i) 1))
                              all-elements))
          doubled-elements (set
                            (filter
                             (fn [i]
                               (= (multiplicity coll i) 2))
                             all-elements))]
      (list (first doubled-elements) (first singular-elements)))))

(defn kuratowski-pair-multiset
  [i]

  (if (equal-seq? i)
    (singleton-multiset (first i))
    (add (repeat-multiset 2 (first i))
         (singleton-multiset (second i)))))

(defn transpose-kuratowski-clan
  [coll]

  (set
   (map
    (comp kuratowski-pair-multiset reverse parse-kuratowski-pair-multiset)
    coll)))

(defn kuratowski-clan
  [coll]

  (set (map kuratowski-pair-multiset coll)))

(defn kuratowski-relation
  [coll]

  (set (map parse-kuratowski-pair-multiset coll)))

; Ontology of kuratowski clans
(def kuratowski-clan?
  (power-set kuratowski-pair-multiset?))

(def irreflexive-kuratowski-clan?
  (power-set order-two-kuratowski-pair-multiset?))

(def antisymmetric-kuratowski-clan?
  (intersection
   kuratowski-clan?
   support-distinct-clan?))

(def asymmetric-kuratowski-clan?
  (intersection
   irreflexive-kuratowski-clan?
   support-distinct-clan?))

(def reflexive-kuratowski-clan?
  (moore-family
   kuratowski-pair-multiset?
   (fn [coll]
     (union
      coll
      (apply union (map (fn [i] (selections (support i) 1)) coll))))))

(def symmetric-kuratowski-clan?
  (moore-family
   kuratowski-pair-multiset?
   (fn [coll]
     (union coll (transpose-kuratowski-clan coll)))))

; Irreducible representations of clan elements
(defn irreducible-representation
  [family elem]

  (let [predecessors (direct-subdimembers family elem)]
    (if (= (count predecessors) 1)
      (let [predecessor (first predecessors)]
        (let [dipredecessors (direct-subdimembers family predecessor)]
          (if (= (count dipredecessors) 1)
            (let [next-coll (frequencies
                             (irreducible-representation family predecessor))]
              (Multiset. {(first (keys next-coll)) (inc (first (vals next-coll)))}))
            (Multiset. {elem 1}))))
      (Multiset. {}))))

(defn clan-representations
  [family]

  (set
   (map
    (fn [i]
      (let [coll (subdimembers family i)]
        (apply
         join
         (map
          (fn [i]
            (irreducible-representation family i))
          coll))))
    (apply union family))))

; Additional functionality
(defn singleton-element-degrees
  [family]

  (Multiset.
   (into
    {}
    (map
     (fn [i]
       [i (degree family i)])
     (apply union (intersection singular-universal? family))))))

(defn mcl
  [clan arg]

  (let [i (meet
           arg
           (apply join clan))]
    (if (contains? clan i)
      i
      (first
       (filter
        (fn [direct-parent]
          (and
           (superbag? (list i direct-parent))
           (every?
            (fn [middle]
              (not
               (and
                (not= middle i)
                (not= middle direct-parent)
                (superbag? (list i middle))
                (superbag? (list middle direct-parent)))))
            clan)))
        clan)))))

(defn madd
  [clan a b]

  (mcl clan (add a b)))










