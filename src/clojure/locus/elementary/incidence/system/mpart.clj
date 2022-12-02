(ns locus.elementary.incidence.system.mpart
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.numeric.ap :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.incidence.system.clan :refer :all])
  (:import [locus.base.logic.core.set Universal Multiset]))

; Enumeration of multiset partitions by properties intrinsic to themselves
; including their signatures as multisets. This includes all multiset 
; partitions as well as partitions into distinct and equal systems.

(defn removability-multiplicity
  [coll part]

  (if (or
       (= (count part) 0)
       (not (superbag? (list part coll))))
    0
    (inc (removability-multiplicity (multiset-difference coll part) part))))

(defn multiset-partitions
  [coll]

  (letfn [(get-partitions [coll]            
            (if (= (count coll) 0)
              (list (multiset '()))
              (cons
               (singleton-multiset coll)
               (let [proper-removable-parts (disj
                                             (disj (power-clan coll) coll)
                                             (multiset '()))]
                 (if (empty? proper-removable-parts)
                   (list)
                   (mapcat
                    (fn [current-removable-part]
                      (let [removability (removability-multiplicity coll current-removable-part)]
                        (mapcat
                         (fn [i]
                           (let [simplified-elem (multiset-difference coll (iterate-multiset current-removable-part i))]
                             (map
                              (fn [partition]
                                (add
                                 partition
                                 (repeat-multiset i current-removable-part)))
                              (get-partitions simplified-elem))))
                         (range 1 (inc removability)))))
                    proper-removable-parts))))))]
    (set (get-partitions coll))))

(defn refinements
  [coll]

  (set
   (map
    (partial apply add)
    (apply
     cartesian-product
     (map
      multiset-partitions
      coll)))))

(defn coarsifications
  [coll]

  (set
   (map
    (fn [partition]
      (multiset (map (partial apply add) partition)))
    (multiset-partitions coll))))

(defn direct-coarsifications
  [coll]

  (set
   (map
    (fn [pair]
      (add
        (singleton-multiset (apply add pair))
        (multiset-difference coll (multiset pair))))
    (union
     (selections (set coll) 2)
     (set
      (for [i (set coll)
            :when (<= 2 (multiplicity coll i))]
        (repeat-multiset 2 i)))))))

(def coarsification?
  (assoc (->Universal
          (fn [[a b]]
            (or
             (= a b)
             (contains? (coarsifications a) b))))
         :arities #{2}
         :query (fn [arg]
                  (case [(count (first arg)) (count (second arg))]
                    [1 0] (let [[[a] []] arg]
                            (coarsifications a))
                    [0 1] (let [[[] [b]] arg]
                            (refinements b))
                    #{}))))

; Multiset partitions into distinct elements
(defn clan-partitions
  [coll]

  (set
   (map
    set
    (filter
     universal?
     (multiset-partitions coll)))))

; Equal partitions are dual to clan partitions
(defn equal-family-partition
  [coll]

  (when (regular-multiset? coll)
    (if (empty? coll)
      #{}
      (let [elems (set coll)
            n (multiplicity coll (first elems))]
        (repeat-multiset n elems)))))

(defn equal-clan-partitions
  [coll]

  (if (empty? coll)
    #{#{}}
    (let [n (apply gcd (signature coll))]
      (set
       (map
        (fn [d]
          (repeat-multiset d (multiset-division coll d)))
        (divisors n))))))

; Get all multiply removable parts of a multiset
(defn multiply-removable-parts
  [coll n]

  (filter
   (fn [i]
     (<= n (removability-multiplicity coll i)))
   (power-clan coll)))

(defn signature-multiset-partitions
  ([coll signature]
   (set (signature-multiset-partitions coll signature #{})))
  ([coll signature forbidden-multisets]
   (cond
     (and (empty? signature) (empty? coll)) '(#{})
     (empty? coll) '()
     (empty? signature) '()
     :else (let [current-multiplicity (first signature)
                 remaining-signature (remove-multiset-element signature current-multiplicity)]
             (mapcat
              (fn [removable-part]
                (if (contains? forbidden-multisets removable-part)
                  '()
                  (let [remaining-multiset (multiset-difference coll (iterate-multiset removable-part current-multiplicity))
                        adjoining-part (repeat-multiset current-multiplicity removable-part)]
                    (map
                     (fn [partition]
                       (add partition adjoining-part))
                     (signature-multiset-partitions
                      remaining-multiset
                      remaining-signature
                      (conj forbidden-multisets removable-part))))))
              (multiply-removable-parts coll current-multiplicity))))))

(defn kuratowski-pair-partitions
  [coll]

  (signature-multiset-partitions coll (multiset '(1 2))))

; Multifamily partitions and their refinements
(defn removable-sets
  [coll]

  (set
   (map
    multiset
    (let [all-keys (set coll)
          key-sets (power-set all-keys)
          nonempty-key-sets (disj key-sets #{})]
      (if (universal? coll)
        (disj nonempty-key-sets all-keys)
        nonempty-key-sets)))))

(defn multifamily-partitions
  [coll]

  (letfn [(get-partitions [coll]            
            (if (= (count coll) 0)
              (list (multiset '()))
              (concat
               (if (universal? coll)
                 (list (singleton-multiset coll))
                 (list))
               (let [proper-removable-parts (removable-sets coll)]
                 (if (empty? proper-removable-parts)
                   (list)
                   (mapcat
                    (fn [current-removable-part]
                      (let [removability (removability-multiplicity coll current-removable-part)]
                        (mapcat
                         (fn [i]
                           (let [simplified-elem (multiset-difference coll (iterate-multiset current-removable-part i))
                                 current-multiset (repeat-multiset i current-removable-part)]
                             (map
                              (fn [partition]
                                (add current-multiset partition))
                              (get-partitions simplified-elem))))
                         (range 1 (inc removability)))))
                    proper-removable-parts))))))]
    (set (get-partitions coll))))

(defn multifamily-refinements
  [coll]

  (letfn [(product-of-finite-sets [& colls]
            (if (empty? colls)
              #{(list)}
              (set
               (mapcat
                (fn [i]
                  (map
                   #(cons i %)
                   (apply product-of-finite-sets (rest colls))))
                (first colls)))))]
    (set
     (map
      (partial apply add)
      (apply
       product-of-finite-sets
       (map
        (comp multifamily-partitions multiset)
        coll))))))

(defn family-partitions
  [coll]

  (set
   (map
    (fn [i]
      (set (map set i)))
    (filter
     universal?
     (multifamily-partitions coll)))))

(defn family-refinements
  [family]

  (set
   (map
    (fn [i]
      (set (map set i)))
    (filter
     universal?
     (multifamily-refinements family)))))

; Egalitarian partitions are dual to family partitions
(defn equal-egalitarian-partitions
  [coll]

  (if (empty? coll)
    #{#{}}
    (let [current-elem (first coll)]
      (set
       (map
        (fn [partition]
          (multiset
           (map
            (fn [i]
              (repeat-multiset i current-elem))
            partition)))
        (all-partitions (count coll)))))))

(defn egalitarian-partitions
  [coll]

  (if (empty? coll)
    #{}
    (map
     (fn [equal-component-partitions]
       (apply add equal-component-partitions))
     (apply
      cartesian-product
      (map
       (fn [i]
         (equal-egalitarian-partitions
          (repeat-multiset (multiplicity coll i) i)))
       (support coll))))))

; Support disjoint partitions are generalisations of set partitions.
(defn support-disjoint-partitions
  [coll]

  (let [supp (support coll)]
    (set
     (map
      (fn [partition]
        (set
         (map
          (fn [part]
            (restrict-multiset coll part))
          partition)))
      (enumerate-set-partitions supp)))))

; Uniform multiclan partitions are precisely
; those that have the same cardinality for each set
(defn uniform-partitions-by
  [coll n]

  (if (empty? coll)
    #{#{}}
    (apply
     union
     (map
      (fn [current-selection]
        (set
          (map
            (fn [partition]
            (add partition (singleton-multiset current-selection)))
            (uniform-partitions-by (multiset-difference coll current-selection) n))))
      (multiset-selections coll n)))))

(defn uniform-partitions
  [coll]

  (let [n (count coll)]
    (apply
     union
     (map
      (fn [d]
        (uniform-partitions-by coll d))
      (divisors n)))))

; Partitions by a cardinality signature
(defn partitions-by-cardinality-signature
  [coll sig]

  (if (empty? coll)
    #{#{}}
    (let [minval (apply min sig)
          mincount (multiplicity sig minval)
          minsum (* mincount minval)]
      (apply
       union
       (for [selection (multiset-selections coll minsum)]
         (let [selection-partitions (uniform-partitions-by selection minval)
               remaining-signature (completely-remove-multiset-element sig minval)
               remaining-partitions (partitions-by-cardinality-signature (multiset-difference coll selection) remaining-signature)]
           (set
            (map
             (fn [[a b]]
               (add a b))
             (cartesian-product remaining-partitions selection-partitions)))))))))

; Partitions by signature families
(defn repeated-signature-selections
  [coll sig n]

  (if (zero? n)
    #{#{}}
    (apply
     union
     (map
      (fn [selection]
        (set
         (map
          (fn [i]
            (add i (singleton-multiset selection)))
          (repeated-signature-selections
           (multiset-difference coll selection)
           sig
           (dec n)))))
      (signature-selections coll sig)))))

; Partitions by a collection of signatures
(defn partitions-by-signatures
  [coll signatures-family]

  (cond
    (empty? coll) #{#{}}
    (empty? signatures-family) #{#{}}
    :else (let [current-signature (first signatures-family)
                current-multiplicity (multiplicity signatures-family current-signature)
                repeated-selections (repeated-signature-selections coll current-signature current-multiplicity)
                remaining-signatures (completely-remove-multiset-element signatures-family current-signature)]
            (apply
             union
             (map
              (fn [part]
                (let [remaining-partitions (partitions-by-signatures
                                            (multiset-difference coll (apply add part))
                                            remaining-signatures)]
                  (set
                   (map
                    (fn [partition]
                      (add partition part))
                    remaining-partitions))))
              repeated-selections)))))

; Kuratowski partitions 
; These in particular refer to all partitions by signature families
; that are defined by the signatures of kuratowski pairs.
(defn kuratowski-partitions
  [coll possible-pairs]

  (cond
    (empty? coll) #{#{}}
    (empty? possible-pairs) #{}
    :else (let [current-pair (first possible-pairs)
                current-multiplicity (removability-multiplicity coll current-pair)]
            (mapcat
             (fn [i]
               (let [current-pair-family (repeat-multiset i current-pair)
                     remaining-partitions (kuratowski-partitions
                                           (multiset-difference coll (apply add current-pair-family))
                                           (rest possible-pairs))]
                 (map
                  (fn [partition]
                    (add partition current-pair-family))
                  remaining-partitions)))
             (range 0 (inc current-multiplicity))))))

(defn all-kuratowski-partitions
  [coll]

  (kuratowski-partitions coll (signature-selections coll (multiset '(1 2)))))

; The theory of kuratowski partitions allows us to relate multisets to certain
; directed graphs. On the other hand, binary family partitions essentially allow
; us to deal with the case of undirected graphs.
(defn binary-multifamily-partitions
  [coll]

  (let [n (count coll)]
    (if (divides? (list 2 n))
      (let [q (int (/ n 2))]
        (repeated-signature-selections
         coll
         (multiset '(1 1))
         q))
      #{})))

(defn binary-family-partitions
  [coll]

  (filter universal? (binary-multifamily-partitions coll)))
