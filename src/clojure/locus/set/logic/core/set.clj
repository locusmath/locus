(ns locus.set.logic.core.set
  (:require [clojure.set])
  (:import (java.util Set)
           (clojure.lang IPersistentSet Seqable MultiFn IRecord)))

; Our most basic notion of is the topos Sets, which is the topos of copresheaves over a single
; point. The elements of Sets are sets and the functions f: A -> B between them. We extend
; the traditional point of view of a function which is that it operates on sets so that
; it can be applied to memory locations described by equivalence relations using the
; partition image function. Our core system therefore makes use of both the traditional
; sets of classical logic and the memory locations described by set partitions. Both
; of them are applicable to functions.
(derive IPersistentSet ::universal)
(derive Set ::universal)

; Entities classification
(defn entity?
  [& args]

  true)

; Multisets
; Multisets are generalizations of sets that allow for the repeated membership of elements in
; the multiset. Multisets form a distributive lattice under the submultiset operation.
(deftype Multiset [multiplicities]
  clojure.lang.Seqable
  (seq [this]
    (if (empty? multiplicities)
      nil
      (apply
        concat
        (map
          (fn [key]
            (repeat (get multiplicities key) key))
          (keys multiplicities)))))

  clojure.lang.Counted
  (count [this]
    (apply + (vals multiplicities)))

  Object
  (equals [this x]
    (and
      (instance? Multiset x)
      (.equals (.multiplicities this) (.multiplicities x))))
  (hashCode [this]
    (hash-combine (hash multiplicities) Multiset))
  (toString [this]
    (str "*{" (clojure.string/join " " (seq this)) "}")))

(defmethod print-method Multiset [^Multiset v ^java.io.Writer w]
  (.write w (.toString v)))

(defn multiset
  [coll]

  (Multiset. (frequencies coll)))

; Universals
; Universals are our terminology for sets. They are counter imposed to particulars, which are
; all objects that are not universals. We use the term proper universal to refer to a universal
; that is not a set. Generally, we use the term class to refer to a class in the sense
; of object-oriented programming on the JVM.
(defrecord Universal [pred]
  clojure.lang.IFn
  (invoke [this obj]
    (pred obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Universal ::universal)

; Seqable universals
; A seqable universal is any universal or predicate that also is seqable in terms of the Clojure
; class system, which means that it implements the clojure.lang.Seqable interface. The
; general class of seqable
(deftype SeqableUniversal [pred choice attrs]
  clojure.lang.Seqable
  (seq [this] (if (empty? choice) nil choice))

  clojure.lang.Counted
  (count [this]
    (if (not (nil? (:count attrs)))
      (min Integer/MAX_VALUE (:count attrs))
      (count (seq this))))

  clojure.lang.IFn
  (invoke [this obj]
    (pred obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive SeqableUniversal ::universal)

; Ontology of universals
(defn intrinsic-universal?
  [x]

  (isa? (type x) ::universal))

(defmulti intrinsic-universal? type)

(defmethod intrinsic-universal? ::universal
  [x] true)

(defmethod intrinsic-universal? :default
  [x]

  (or
    (fn? x)
    (= (type x) MultiFn)))

(defn intrinsic-multiset?
  [coll]

  (instance? Multiset coll))

(defn multiset?
  [x]

  (or
    (intrinsic-universal? x)
    (intrinsic-multiset? x)))

(defmulti universal? type)

(defmethod universal? ::universal
  [x] true)

(defmethod universal? :default
  [x]

  (or
    (intrinsic-universal? x)
    (and
      (multiset? x)
      (= (count x) (count (set (keys (.multiplicities x))))))))

(defn seqable-universal?
  [x]

  (and
    (universal? x)
    (not (instance? IRecord x))
    (seqable? x)))

; Upto
; An upto is the set of all numbers less then a given positive integer n. So it is equivalent to a
; range starting with zero and having a step value of one at each point.
(deftype Upto [n]
  clojure.lang.Seqable
  (seq [this] (range n))

  clojure.lang.Counted
  (count [this] n)

  Object
  (toString [this] (str (set (seq this))))

  clojure.lang.IFn
  (invoke [this arg]
    (and
      (integer? arg)
      (not (neg? arg))
      (< arg n)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Upto ::universal)

(defmethod print-method Upto [^Upto v ^java.io.Writer w]
  (.write w (.toString v)))

; Range sets
; A range set is a variation of a Clojure range, but now implemented to be a set or a universal
; so that it can be treated to be part of our set theory subsystem.
(deftype RangeSet [min max]
  clojure.lang.Seqable
  (seq [this] (range min max))

  clojure.lang.Counted
  (count [this] (- max min))

  Object
  (toString [this] (str (set (seq this))))

  clojure.lang.IFn
  (invoke [this arg]
    (and
      (integer? arg)
      (<= min arg)
      (< arg max)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive RangeSet ::universal)

(defmethod print-method RangeSet [^RangeSet v ^java.io.Writer w]
  (.write w (.toString v)))

; Lattice operations of sets
(defmulti intersection*
          (fn [a b] (set [(type a) (type b)])))

(defmethod intersection* :default
  [a b]

  (cond
    (and (set? a) (set? b)) (clojure.set/intersection a b)
    (set? a) (set (filter b a))
    (set? b) (set (filter a b))
    (seqable-universal? a) (SeqableUniversal.
                             (fn [i] (and (a i) (b i)))
                             (filter b (seq a))
                             {})
    (seqable-universal? b) (SeqableUniversal.
                             (fn [i] (and (a i) (b i)))
                             (filter a (seq b))
                             {})
    :else (fn [& args]
            (and (apply a args) (apply b args)))))

(defmulti union*
          (fn [a b] (set [(type a) (type b)])))

(defmethod union* :default
  [a b]

  (cond
    (and (set? a) (set? b)) (clojure.set/union a b)
    (and (set? a) (seqable-universal? b))
    (SeqableUniversal.
      (fn [i] (or (contains? a i) (b i)))
      (concat (seq a) (seq b))
      {})
    (and (seqable-universal? a) (set? b))
    (SeqableUniversal.
      (fn [i] (or (a i) (contains? b i)))
      (concat (seq a) (seq b))
      {})
    (and (seqable-universal? a) (seqable-universal? b))
    (SeqableUniversal.
      (fn [i] (or (a i) (b i)))
      (concat (seq a) (seq b))
      {})
    :else (fn [& args]
            (or (apply a args) (apply b args)))))

(def union
  (fn
    ([] #{})
    ([a] a)
    ([a b] (union* a b))
    ([a b & more] (reduce union* (union* a b) more))))

(def intersection
  (fn
    ([] entity?)
    ([a] a)
    ([a b] (intersection* a b))
    ([a b & more] (reduce intersection* (intersection* a b) more))))

; Difference operations
(def difference
  (fn
    ([a] a)
    ([a b]
     (cond
       (and (set? a) (set? b)) (clojure.set/difference a b)
       (set? b) (intersection a (complement (partial contains? b)))
       :else (intersection a (complement b))))
    ([a b & more] (reduce difference (difference a b) more))))

(def symmetric-difference
  (fn
    ([] #{})
    ([a] a)
    ([a b] (difference (union a b) (intersection a b)))
    ([a b & more] (reduce symmetric-difference (symmetric-difference a b) more))))

; The dimembers of a family of sets are all the members of members of the family
(defmulti dimembers type)

(defmethod dimembers :default
  [coll] (apply union coll))

; Powers
(defn power-of-two
  [n]

  (bigint (.pow (BigInteger/valueOf 2) n)))

(defn power-of-three
  [n]

  (bigint (.pow (BigInteger/valueOf 3) n)))

(defn power-of-four
  [n]

  (bigint (.pow (BigInteger/valueOf 4) n)))

; Seqable power set
(defn convert-to-bits
  [size n]

  (if (<= n Integer/MAX_VALUE)
    (vec
      (concat
        (map
          (fn [i]
            (bit-and (bit-shift-right n i) 1))
          (range (min 31 size)))
        (repeat (max 0 (- size 31)) 0)))))

(defn enumerate-subsets
  [coll]

  (let [size (count coll)
        ordered-coll (vec (apply list coll))]
    (map
      (fn [i]
        (set
          (let [bits (convert-to-bits size i)]
            (for [i (range size)
                  :when (= 1 (nth bits i))]
              (nth ordered-coll i)))))
      (range (bigint (.pow (BigInteger/valueOf 2) size))))))

(defn seqable-power-set
  [coll]

  (SeqableUniversal.
    (fn [i] (= i (intersection coll i)))
    (enumerate-subsets coll)
    {:count (power-of-two (count coll))}))

(defn power-set
  [coll]

  (cond
    (seqable-universal? coll) (if (<= (count coll) 32)
                                (set (enumerate-subsets coll))
                                (seqable-power-set coll))
    (intrinsic-multiset? coll) (power-set (set coll))
    :else (assoc (Universal. (fn [subcoll]
                               (and
                                 (universal? subcoll)
                                 (= (set subcoll) (set (intersection (set subcoll) coll))))))
            :closure identity)))

; Super sets are dual to power sets
(defn super-set
  [coll]

  (if (= coll entity?)
    #{entity?}
    (assoc (Universal.
             (fn [parent-coll]
               (= coll (intersection coll parent-coll))))
      :closure (fn [subcoll]
                 (union coll subcoll)))))

; Universals inclusion ordering
(defn equal-universals?
  [a b]

  (or
    (= a b)
    (and
      (every? a b)
      (every? b a))))

(def superset?
  (assoc (Universal.
           (fn [[a b]]
             (equal-universals? a (intersection a b))))
    :arities #{2}
    :join union
    :meet intersection
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[coll] []] arg]
                       (super-set coll))
               [0 1] (let [[[] [coll]] arg]
                       (power-set coll))
               #{}))))

; Power sets
; A power set is a set of all subsets of a given set. It always has a cardinality which is a
; power of two. A PowerSet is a universal and it implements the Seqable interface.
(deftype PowerSet [coll]
  clojure.lang.Seqable
  (seq [this]
    (enumerate-subsets coll))

  clojure.lang.Counted
  (count [this]
    (power-of-two (count coll)))

  Object
  (toString [this]
    (str "ℙ(" coll ")"))

  clojure.lang.IFn
  (invoke [this obj]
    (superset? (list obj coll)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive PowerSet ::universal)

(defmethod print-method PowerSet [^PowerSet v ^java.io.Writer w]
  (.write w (.toString v)))

(defmethod dimembers PowerSet
  [^PowerSet ps] (.coll ps))

(defmethod intersection* #{PowerSet}
  [a b]

  (PowerSet. (intersection (.coll a) (.coll b))))

; Seqable filter
(defn seqable-filter
  [pred parent]

  (->SeqableUniversal
    pred
    (filter pred parent)
    {}))

; Enumeration of subsets by predicates
(defn subsets
  [pred? family]

  (set
    (filter
      pred?
      (power-set family))))

; Support and multiplicity for multisets
(defmulti support type)

(defmethod support Multiset
  [^Multiset coll]

  (set (keys (.-multiplicities coll))))

(defmethod support ::universal
  [x] x)

(defmulti multiplicity (fn [a b] (type a)))

(defmethod multiplicity ::universal
  [coll x]

  (if (boolean (coll x))
    1
    0))

(defmethod multiplicity Multiset
  [^Multiset coll, x]

  (or (get (.-multiplicities coll) x) 0))

; Signatures of multisets
(defmulti signature type)

(defmethod signature Multiset
  [^Multiset coll]

  (Multiset. (frequencies (vals (.-multiplicities coll)))))

(defmethod signature ::universal
  [coll]

  (Multiset.
    (if (= (count coll) 0)
      {}
      {1 (count coll)})))

; Multiset creator functions
(defn repeat-multiset
  [n a]

  (Multiset.
    (if (zero? n)
      {}
      {a n})))

(defn singleton-multiset
  [a]

  (Multiset. {a 1}))

(defn regular-multiset
  [coll n]

  (Multiset.
    (zipmap
      coll
      (repeat (count coll) n))))

; Lattice operations on multisets
(defn join-multisets
  ([] (Multiset. {}))
  ([a] a)
  ([a b]
   (Multiset.
     (let [new-keys (union (support a)
                           (support b))]
       (zipmap
         new-keys
         (map
           (fn [key]
             (max (multiplicity a key)
                  (multiplicity b key)))
           new-keys)))))
  ([a b & more] (reduce join-multisets (join-multisets a b) more)))

(defn meet-multisets
  ([] (Multiset. {}))
  ([a] a)
  ([a b]
   (Multiset.
     (let [new-keys (intersection (support a)
                                  (support b))]
       (zipmap
         new-keys
         (map
           (fn [key]
             (min (multiplicity a key)
                  (multiplicity b key)))
           new-keys)))))
  ([a b & more] (reduce meet-multisets (meet-multisets a b) more)))

; Algebraic combinational operations
(defn add
  ([] (Multiset. {}))
  ([a] a)
  ([a b]
   (Multiset.
     (let [new-keys (union (support a)
                           (support b))]
       (zipmap
         new-keys
         (map
           (fn [key]
             (+ (multiplicity a key)
                (multiplicity b key)
                ))
           new-keys)))))
  ([a b & more] (reduce add (add a b) more)))

(defn multiset-difference
  [a b]

  (Multiset.
    (into
      {}
      (for [i (union (support a)
                     (support b))
            :let [n (- (multiplicity a i)
                       (multiplicity b i))]
            :when (<= 1 n)]
        [i n]))))

(defn remove-multiset-element
  [coll elem]

  (multiset-difference coll (singleton-multiset elem)))

(defn degrees
  [family]

  (apply add family))

(defn degree
  [family elem]

  (apply + (map (fn [i] (multiplicity i elem)) family)))

; Iterate and divide multisets
(defn iterate-multiset
  [coll n]

  (cond
    (= n 0) (multiset '())
    (= n 1) coll
    :else (->Multiset
            (into
              {}
              (if (intrinsic-universal? coll)
                (map
                  (fn [i]
                    [i n])
                  coll)
                (map
                  (fn [[i v]]
                    [i (* n v)])
                  (.multiplicities coll)))))))

; Division and remainder of multisets
(defn multiset-division
  [coll divisor]

  (Multiset.
    (into
      {}
      (for [elem (support coll)
            :let [n (multiplicity coll elem)]
            :when (<= divisor n)]
        [elem (quot n divisor)]))))

(defn multiset-remainder
  [coll divisor]

  (Multiset.
    (into
      {}
      (for [elem (support coll)
            :let [n (multiplicity coll elem)]
            :when (not (zero? (mod n divisor)))]
        [elem (mod n divisor)]))))

; Multisets inclusion ordering
(defn enumerate-submultisets
  [coll]

  (letfn [(place-system [coll]
            (fn [j]
              (map
                (fn [i]
                  (mod (quot j (apply * (take i coll)))
                       (nth coll i)))
                (range (count coll)))))]
    (let [parts-count (apply * (map inc (signature coll)))
          ordered-keys (seq (set coll))
          ordered-key-sizes (map
                              (fn [i]
                                (inc (multiplicity coll (nth ordered-keys i))))
                              (range (count ordered-keys)))
          func (place-system ordered-key-sizes)]
      (map
        (fn [i]
          (let [current-coll (func i)]
            (apply
              add
              (map
                (fn [i]
                  (repeat-multiset (nth current-coll i) (nth ordered-keys i)))
                (range (count ordered-keys))))))
        (range parts-count)))))

(defn power-clan
  [coll]

  (if (seqable-universal? coll)
    (power-set coll)
    (set (enumerate-submultisets coll))))

(def superbag?
  (assoc (->Universal
           (fn [[a b]]
             (and
               (superset? (list (support a) (support b)))
               (every?
                 (fn [key]
                   (<= (multiplicity a key) (multiplicity b key)))
                 (support a)))))
    :arities #{2}
    :join join-multisets
    :meet meet-multisets
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[coll] []] arg]
                       (fn [i]
                         (superbag? (list coll i))))
               [0 1] (let [[[] [coll]] arg]
                       (power-clan coll))
               #{}))))

(defn seqable-power-clan
  [coll]

  (SeqableUniversal.
    (fn [i] (superbag? (list i coll)))
    (enumerate-submultisets coll)
    {:count (apply * (map inc (signature coll)))}))

; We will now describe a wide range of techniques of getting special
; subsets and submultisets of a set or multiset. In particular, we can get all
; submultisets with a given cardinality, signature, order, support,
; maximum multiplicity, or other property.
(defn restrict-multiset
  [multiset remaining-elements]

  (if (seqable-universal? multiset)
    (intersection multiset remaining-elements)
    (Multiset.
      (into
        {}
        (map
          (fn [key]
            [key (multiplicity multiset key)])
          remaining-elements)))))

(defn completely-remove-multiset-element
  [coll elem]

  (Multiset.
    (let [new-keys (seq (disj (support coll) elem))]
      (zipmap
        new-keys
        (map
          (fn [i] (multiplicity coll i))
          new-keys)))))

(defn completely-remove-multiset-elements
  [multiset coll]

  (restrict-multiset
    multiset
    (difference (support multiset) coll)))

; Get all restrictions of a multiset
(defn multiset-restrictions
  [coll]

  (set
    (map
      (fn [i]
        (restrict-multiset coll i))
      (power-set (support coll)))))

; Combinatorial techniques for the enumeration of collections of subsets
; and submultisets of multisets.
(defn binomial-coefficient
  [n k]

  (apply
    *
    (map
      (fn [i]
        (/ (+ n 1 (- i)) i))
      (range 1 (inc k)))))

(defn selections
  [coll k]

  (letfn [(index-combinations [coll k]
            (if-not (< 0 k (inc (count coll)))
              #{#{}}
              (let [ordered-coll (seq coll)
                    first-elem (first ordered-coll)
                    rest-coll (rest ordered-coll)]
                (union
                  (set
                    (filter
                      (complement empty?)
                      (index-combinations rest-coll k)))
                  (set
                    (map
                      #(conj % first-elem)
                      (index-combinations rest-coll (dec k))))))))]
    (cond
      (= k 0) #{#{}}
      (not (intrinsic-universal? coll)) (selections (set coll) k)
      (not (seqable-universal? coll)) (fn [selection]
                                        (and
                                          (universal? selection)
                                          (= (count selection) k)
                                          (every? coll selection)))
      (= k 1) (set (map (fn [i] #{i}) coll))
      (< (count coll) k) #{}
      (= k (count coll)) #{coll}
      :else (set (index-combinations (seq coll) k)))))

; Seqable selections
(def indexing
  (fn indexing*
    ([f n] (indexing* f n 0))
    ([f n i]
     (if (< n (f i))
       (list i (- n (if (zero? i) 0 (f (dec i)))))
       (indexing* f n (inc i))))))

(defn nth-selection
  [k n]

  (cond
    (= k 0) #{}
    (= k 1) #{n}
    :else (let [[a b] (indexing #(binomial-coefficient % k) n)]
            (conj (nth-selection (dec k) b) (dec a)))))

(defn enumerate-selections
  [coll k]

  (let [size (binomial-coefficient (count coll) k)
        ordered-coll (vec (apply list coll))]
    (map
      (fn [i]
        (let [selection (nth-selection k i)]
          (set (map ordered-coll selection))))
      (range size))))

(defn seqable-selections
  [coll k]

  (SeqableUniversal.
    (fn [selection]
      (and
        (universal? selection)
        (= (count selection) k)
        (superset? (list selection coll))))
    (enumerate-selections coll k)
    {:count (binomial-coefficient (count coll) k)}))

; Seqable multiselections
(defn multiselection
  [parent-coll nums]

  (cond
    (empty? nums) #{}
    (set? parent-coll) (apply
                         union
                         (map
                           (fn [i]
                             (selections parent-coll i))
                           nums))
    :else (intersection
            (power-set parent-coll)
            (comp (if (set? nums) (partial contains? nums) nums) count))))

(defn seqable-multiselection
  [coll nums]

  (apply union (map (partial seqable-selections coll) nums)))

; Multiset selections
(defn number-of-multiset-selections
  [signature n]

  (if (empty? signature)
    (if (zero? n)
      1
      0)
    (case n
      0 1
      1 (count signature)
      (let [elem (first signature)
            remaining-multiplicities (rest signature)]
        (apply +
               (map
                 (fn [i]
                   (number-of-multiset-selections remaining-multiplicities (- n i)))
                 (range (inc (min elem n)))))))))

(defn multiset-selections
  [parent num]

  (cond
    (zero? num) #{(multiset '())}
    (< (count parent) num) #{}
    :else (let [current-elem (first (support parent))
                elem-multiplicity (multiplicity parent current-elem)
                allowed-multiplicity (min num elem-multiplicity)
                remaining-multiset (completely-remove-multiset-element
                                     parent
                                     current-elem)]
            (apply
              union
              (map
                (fn [current-multiplicity]
                  (set
                    (let [current-multiset (repeat-multiset current-multiplicity current-elem)]
                      (map
                        (fn [current-selection]
                          (add current-selection current-multiset))
                        (multiset-selections
                          remaining-multiset
                          (- num current-multiplicity))))))
                (range 0 (inc allowed-multiplicity)))))))

; Multiset multiselections
(defn multiset-multiselections
  [parent nums]

  (apply union (map (partial multiset-selections parent) nums)))

; Signature selections
(defn number-of-signature-selections
  [parent-signature child-signature]

  (letfn [(enumerate [coll sorted-signature]
            (if (empty? sorted-signature)
              1
              (if (empty? coll)
                0
                (let [smallest-multiplicity (first sorted-signature)]
                  (apply
                    +
                    (for [i coll
                          :when (<= smallest-multiplicity i)]
                      (enumerate
                        (remove-multiset-element coll i)
                        (rest sorted-signature))))))))]
    (enumerate parent-signature (sort < (seq child-signature)))))

(defn signature-selections
  [coll sig]

  (let [n (apply + sig)]
    (cond
      (zero? n) #{#{}}
      (= n 1) (selections (support coll) 1)
      :else (let [maxval (apply max sig)
                  maxcount (multiplicity sig maxval)
                  permissible-elements (set
                                         (filter
                                           (fn [i]
                                             (<= maxval (multiplicity coll i)))
                                           (support coll)))
                  permissible-subsets (selections permissible-elements maxcount)]
              (apply
                union
                (for [selection permissible-subsets]
                  (let [remaining-elements (difference (support coll) selection)
                        remaining-selections (signature-selections
                                               (restrict-multiset coll remaining-elements)
                                               (completely-remove-multiset-element sig maxval))
                        selection-multiset (regular-multiset selection maxval)]
                    (set
                      (map
                        (fn [i]
                          (add i selection-multiset))
                        remaining-selections)))))))))

; Order selections
(defn interval-clan
  [child-multiset parent-multiset]

  (let [difference-multiset (multiset-difference parent-multiset child-multiset)]
    (set
      (map
        (fn [coll]
          (add child-multiset coll))
        (power-clan difference-multiset)))))

(defn logical-multiset-reductions
  "Get all submultisets with a given support."
  [parent coll]

  (interval-clan (set coll) (restrict-multiset parent coll)))

(defn order-selections
  [parent num]

  (let [underlying-set (set parent)
        underlying-selections (selections underlying-set num)]
    (apply
      union
      (set
        (map
          (fn [underlying-selection]
            (logical-multiset-reductions
              parent
              underlying-selection))
          underlying-selections)))))

(defn order-multiselections
  [parent nums]

  (apply
    union
    (map
      (fn [num]
        (order-selections parent num))
      nums)))

(defn equal-submultisets
  [coll]

  (order-selections coll 1))

(defn wide-submultisets
  [coll]

  (interval-clan (support coll) coll))

; Universal and powerful submultisets
(defn universal-part
  [coll]

  (set
    (filter
      (fn [i]
        (= (multiplicity coll i) 1))
      (support coll))))

(defn powerful-part
  [coll]

  (Multiset.
    (into
      {}
      (for [i coll
            :let [n (multiplicity coll i)]
            :when (<= 2 n)]
        [i n]))))

; We can get the maximum multiplicity component of a multiset
(defn reduce-maximum-multiplicity
  [coll n]

  (Multiset.
    (into
      {}
      (for [i coll
            :let [m (min (multiplicity coll i) n)]]
        [i m]))))

; Underlying chain multiset
(defn underlying-chain-multiset
  "Reduce the multiplicities set to a range."
  [coll]

  (let [keys (support coll)
        multiplicities (sort
                         <
                         (map
                           (fn [key] (multiplicity coll key))
                           keys))]
    (apply
      add
      (map
        (fn [key]
          (repeat-multiset
            (inc
              (first
                (filter
                  (fn [i]
                    (= (nth multiplicities i)
                       (multiplicity coll key)))
                  (range (count multiplicities)))))
            key))
        keys))))

; We need some way of associating a a collection of multisets to a set
(defn number-of-selected-multisets
  [n k]

  (binomial-coefficient (+ n k (- 1)) k))

(defn supported-multisets
  [coll n]

  (if (and (empty? coll) (not (zero? n)))
    #{}
    (case n
      0 #{#{}}
      1 (set (map singleton-multiset coll))
      (apply
        union
        (let [current-element (first coll)
              remaining-elements (disj coll current-element)]
          (map
            (fn [i]
              (set
                (map
                  (fn [multiset]
                    (add multiset (repeat-multiset i current-element)))
                  (supported-multisets remaining-elements (- n i)))))
            (range (inc n))))))))

; Multiset partitions
(defn support-partition
  "Partitionize the elements of a multiset by multiplicities"
  [coll]

  (set
    (map
      (fn [i]
        (set
          (filter
            (fn [j]
              (= (multiplicity coll j) i))
            coll)))
      (set (signature coll)))))

; Distributions
(defn relative-multiplicity
  [coll key]

  (if (not (contains? (support coll) key))
    0
    (/ (multiplicity coll key)
       (count coll))))

(defn dist
  [coll]

  (into
    {}
    (let [size (count coll)]
      (map
        (fn [i]
          [i (/ (multiplicity coll i) size)])
        (support coll)))))

(defn mark
  "Multiset of relative frequencies of a multiset"
  [coll]

  (let [size (count coll)]
    (multiset
      (map
        (fn [i]
          (/ (multiplicity coll i) size))
        (support coll)))))

(defn multiplicities-map
  [coll]

  (into
    {}
    (map
      (fn [i]
        [i (multiplicity coll i)])
      (support coll))))

; Ordinal numbers
; An ordinal number is a pure set theoretic representation of the positive integers. It can be
; created by getting a finite total order and then representing all of its elements as members
; of a distributive lattice, and then recursively repeating that processes until all you get is
; sets. The resulting ordinal is a pure set. As it grows exponentially, it is far better to
; represent an ordinal using a class then a direct representation.
(deftype Ordinal [n]
  clojure.lang.Seqable
  (seq [this] (if (zero? n) nil (map #(Ordinal. %) (range n))))

  clojure.lang.Counted
  (count [this] (min Integer/MAX_VALUE n))

  Object
  (equals [this x]
    (and
      (instance? Ordinal x)
      (= (count this) (count x))))
  (hashCode [this]
    (hash-combine (hash n) Ordinal))
  (toString [this]
    (str "#" n))

  clojure.lang.IFn
  (invoke [this obj]
    (and (instance? Ordinal obj)
         (< (count obj) n)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Ordinal ::universal)

(defmethod union* #{Ordinal}
  [a b] (Ordinal. (max (count a) (count b))))

(defmethod intersection* #{Ordinal}
  [a b] (Ordinal. (min (count a) (count b))))

(defmethod print-method Ordinal [a w] (.write w (str "#" (.n a))))

; Representation of natural numbers as multisets
(defn tally
  [n]

  (repeat-multiset n 1))

; Integers
(def natural-number?
  (intersection
    integer?
    (complement neg?)))

(def positive-integer?
  (intersection
    integer?
    pos?))

(def negative-integer?
  (intersection
    neg?
    integer?))

; The lattice of positive integers under the natural total ordering
; the min and max operations define the total ordering itself
(defn subnaturals
  [n]

  (set (range (inc n))))

(def supernatural?
  (assoc (->Universal
           (fn [[a b]]
             (and
               (natural-number? a)
               (natural-number? b)
               (<= a b))))
    :arities #{2}
    :join max
    :meet min
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[a] []] arg]
                       (if (natural-number? a)
                         (fn [i]
                           (and
                             (natural-number? i)
                             (<= a i)))
                         #{}))
               [0 1] (let [[[] [b]] arg]
                       (if (natural-number? b)
                         (set (range (inc b)))
                         #{}))
               #{}))))

(def superinteger?
  (assoc (->Universal
           (fn [[a b]]
             (and
               (integer? a)
               (integer? b)
               (<= a b))))
    :join max
    :meet min
    :arities #{2}))

; The multiset lattice of positive integers under divisibility
; The factors converts the positive integer into its corresponding multiset
(defn gcd
  ([] 0)
  ([a] a)
  ([a b]
   (if (zero? b)
     a
     (gcd b (mod a b))))
  ([a b & more]
   (reduce gcd (gcd a b) more)))

(defn lcm
  ([] 1)
  ([a] a)
  ([a b]
   (cond (or (= a Double/POSITIVE_INFINITY)
             (= b Double/POSITIVE_INFINITY))
         Double/POSITIVE_INFINITY
         :else (/ (Math/abs (* a b))
                  (gcd a b))))
  ([a b & more]
   (reduce lcm (lcm a b) more)))

(defn divisors
  [n]

  (let [lower-divisors (filter
                         (fn [i]
                           (zero? (mod n i)))
                         (range 1 (inc (int (Math/sqrt n)))))
        upper-divisors (map
                         (partial / n)
                         lower-divisors)]
    (union (set lower-divisors) (set upper-divisors))))

(def divides?
  (assoc (Universal.
           (fn [[a b]]
             (and
               (natural-number? a)
               (natural-number? b)
               (zero? (mod b a)))))
    :arities #{2}
    :join lcm
    :meet gcd
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [0 1] (let [[[] [b]] arg]
                       (divisors b))
               [1 0] (let [[[a] []] arg]
                       (fn [b]
                         (and
                           (natural-number? a)
                           (natural-number? b)
                           (zero? (mod a b)))))
               #{}))))

; Rational numbers
; Rational numbers a subclass of magnitude numbers. Non negative
; proper rational numbers are an important subclass dealing
; with probability. We will deal with these in more
; detail in a separate file.
(def negative-rational-number?
  (intersection
    neg?
    rational?))

(def nonnegative-rational-number?
  (intersection
    rational?
    (complement pos?)))

(def positive-rational-number?
  (intersection
    pos?
    rational?))

(defn nonnegative-proper-rational-number?
  [n]

  (and
    (rational? n)
    (<= 0 n 1)))

(defn positive-proper-rational-number?
  [n]

  (and
    (rational? n)
    (< 0 n)
    (<= n 1)))

(def superrational?
  (assoc (->Universal
           (fn [[a b]]
             (and
               (rational? a)
               (rational? b)
               (<= a b))))
    :join max
    :meet min
    :arities #{2}))

(defmulti real-number? type)

(defmethod real-number? :default
  [x] (number? x))

; Factorial
(defn factorial
  [n]

  (loop [i 1N
         rval 1N]
    (if (<= i n)
      (recur (inc i) (* rval i))
      rval)))

(defn number-of-permutations
  [coll]

  (let [sig (signature coll)]
    (/ (factorial (apply + sig))
       (apply * (map factorial sig)))))

(def number-of-multiplicity-permutations
  (comp number-of-permutations signature))

; We may as well have related factorials
(defn falling-factorial
  [n k]

  (apply *
         (map
           (fn [i]
             (- n i))
           (range k))))

(defn rising-factorial
  [n k]

  (apply *
         (map
           (fn [i]
             (+ n i))
           (range k))))

; Complete lagrange families
(defn complete-lagrange-family
  [coll]

  (if (empty? coll)
    #{}
    (multiselection
      coll
      (set (divisors (count coll))))))

; All subsets in an interval that can be part of a lagrange family
(defn lagrange-interval
  [lower-coll upper-coll]

  (let [lower-cardinality (count lower-coll)
        upper-cardinality (count upper-coll)
        remaining-coll (difference upper-coll lower-coll)
        nums (set
               (filter
                 (fn [i]
                   (divides?
                     (list (+ lower-cardinality i) upper-cardinality)))
                 (range (inc (count remaining-coll)))))]
    (set
      (map
        (fn [additional-elements]
          (set (union lower-coll additional-elements)))
        (multiselection remaining-coll nums)))))

; Signature properties
(defn repetitiveness
  [coll]

  (- (count (multiset coll))
     (count (set coll))))

(defn multiset-order
  [coll]

  (count (set coll)))

(defn maximum-multiplicity
  [coll]

  (if (= (count coll) 0)
    0
    (apply max (signature coll))))

(defn minimum-multiplicity
  [coll]

  (if (= (count coll) 0)
    0
    (apply min (signature coll))))

(defn unequalness
  [coll]

  (- (count coll)
     (maximum-multiplicity coll)))

(defn multiset-exponent
  "This dual to the distribution of the multiset."
  [coll]

  (if (= (count coll) 0)
    0
    (apply gcd (signature coll))))

(defn number-of-multiset-parts
  [coll]

  (apply * (map inc (signature coll))))

; Unordered collections
; this is the beginning of our extensive system
; of classification of multisets based upon their
; signatures and related properties. This leads
; to the ontology of multisets.
(defn cardinality-classification
  [cardinalities]

  (cond
    (set? cardinalities) (fn [coll]
                           (and
                             (universal? coll)
                             (contains? cardinalities (count coll))))
    :else (fn [coll]
            (and
              (universal? coll)
              (cardinalities (count coll))))))

(def singular-universal?
  (cardinality-classification #{1}))

(def size-two-universal?
  (cardinality-classification #{2}))

(def size-three-universal?
  (cardinality-classification #{3}))

(def size-four-universal?
  (cardinality-classification #{4}))

(def unique-universal?
  (cardinality-classification #{0 1}))

(def max-size-two-universal?
  (cardinality-classification #{0 1 2}))

(def max-size-three-universal?
  (cardinality-classification #{0 1 2 3}))

(def max-size-four-universal?
  (cardinality-classification #{0 1 2 3 4}))

; Multiset cardinality classification
(defn size-two-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (count coll) 2)))

(defn size-three-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (count coll) 3)))

(defn size-four-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (count coll) 4)))

(defn max-size-two-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (count coll) 2)))

(defn max-size-three-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (count coll) 3)))

(defn max-size-four-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (count coll) 4)))

; Minimum cardinality multiset
(defn nonempty-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= 1 (count coll))))

(defn composite-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= 2 (count coll))))

; Equal multisets
(defn equal-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (count (set coll)) 1)))

(def size-two-equal-multiset?
  (intersection
    equal-multiset?
    size-two-multiset?))

(def size-three-equal-multiset?
  (intersection
    equal-multiset?
    size-three-multiset?))

(def size-four-equal-multiset?
  (intersection
    equal-multiset?
    size-four-multiset?))

(def max-size-two-equal-multiset?
  (intersection
    equal-multiset?
    max-size-two-multiset?))

(def max-size-three-equal-multiset?
  (intersection
    equal-multiset?
    max-size-three-multiset?))

(def max-size-four-equal-multiset?
  (intersection
    equal-multiset?
    max-size-four-multiset?))

; Weak multisets
; Weak multisets include both the equal
; multisets we have been describing so far
; as well as the other multiset types
(defn weak-multiset?
  [coll]

  (or
    (equal-multiset? coll)
    (universal? coll)))

; Classification of multisets by order
; the order is the number of distinct elements
(defn max-order-two-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (multiset-order coll) 2)))

(defn max-order-three-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (multiset-order coll) 3)))

(defn max-order-four-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (multiset-order coll) 4)))

(defn order-two-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (multiset-order coll) 2)))

(defn order-three-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (multiset-order coll) 3)))

(defn order-four-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (multiset-order coll) 4)))

; Max multiplicity multisets
(defn max-multiplicity-two-multiset?
  [coll]

  (and
    (multiset? coll)
    (every? (fn [i] (<= i 2)) (signature coll))))

(defn max-multiplicity-three-multiset?
  [coll]

  (and
    (multiset? coll)
    (every? (fn [i] (<= i 3)) (signature coll))))

(defn max-multiplicity-four-multiset?
  [coll]

  (and
    (multiset? coll)
    (every? (fn [i] (<= i 4)) (signature coll))))

; Classification of multisets based upon their higher signatures
; this leads to notions of regularity and irregularity
; a notable aspect of higher signatures is that they are
; related to distributions
(defn regular-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= (count (set (signature coll))) 1)))

(defn antiregular-multiset?
  [coll]

  (and
    (multiset? coll)
    (= (count (set (signature coll))) (count (signature coll)))))

; Minimum multiplicity corank
(defn powerful-multiset?
  [coll]

  (and
    (multiset? coll)
    (every? (fn [i] (<= 2 (multiplicity coll i))) (set coll))))

(defn three-powerful-multiset?
  [coll]

  (and
    (multiset? coll)
    (every? (fn [i] (<= 3 (multiplicity coll i))) (set coll))))

(defn four-powerful-multiset?
  [coll]

  (and
    (multiset? coll)
    (every? (fn [i] (<= 4 (multiplicity coll i))) (set coll))))

; Chain multisets are also based upon the classification of
; the multiplicities set. It checks if the set is a range.
(defn chain-multiset?
  "The multiplicities use a range."
  [coll]

  (let [nums (set (signature coll))]
    (= nums (set (range 1 (inc (count nums)))))))

; Near universal and near equal multisets
(defn near-universal?
  [coll]

  (or
    (universal? coll)
    (= (repetitiveness coll) 1)))

(defn near-equal-multiset?
  [coll]

  (or
    (equal-multiset? coll)
    (= (unequalness coll) 1)))

; Special classes of regular multisets
(defn power-set-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (let [order (multiset-order coll)
          mult (power-of-two (dec order))]
      (every?
        (fn [i]
          (= (multiplicity coll i) mult))
        (set coll)))))

(defn complete-binary-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (let [order (multiset-order coll)
          mult (dec order)]
      (every?
        (fn [i]
          (= (multiplicity coll i) mult))
        (set coll)))))

(defn complete-ternary-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (let [order (multiset-order coll)
          mult (binomial-coefficient (dec order) 2)]
      (every?
        (fn [i]
          (= (multiplicity coll i) mult))
        (set coll)))))

(defn complete-quaternary-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (let [order (multiset-order coll)
          mult (binomial-coefficient (dec order) 3)]
      (every?
        (fn [i]
          (= (multiplicity coll i) mult))
        (set coll)))))

; Progression multisets
; These are antiregular because each multiplicity is different
; these are also the only antiregular multisets with set theoretic partitions
(defn progression-multiset?
  [coll]

  (and
    (antiregular-multiset? coll)
    (= (set (signature coll))
       (set (range 1 (inc (multiset-order coll)))))))

; Additional classes of progressions
(def max-order-two-progression-multiset?
  (intersection
    progression-multiset?
    max-order-two-multiset?))

(def max-order-three-progression-multiset?
  (intersection
    progression-multiset?
    max-order-three-multiset?))

(def max-order-four-progression-multiset?
  (intersection
    progression-multiset?
    max-order-four-multiset?))

(def order-three-progression-multiset?
  (intersection
    progression-multiset?
    order-three-multiset?))

(def order-four-progression-multiset?
  (intersection
    progression-multiset?
    order-four-multiset?))

(defn kuratowski-pair-multiset?
  [coll]

  (and
    (progression-multiset? coll)
    (or (= (multiset-order coll) 1)
        (= (multiset-order coll) 2))))

(def order-two-kuratowski-pair-multiset?
  (intersection
    kuratowski-pair-multiset?
    order-two-multiset?))

; Perfect powers
(defn double-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (even? (multiset-exponent coll))))

(defn triple-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (= (mod (multiset-exponent coll) 3) 0)))

(defn quadruple-multiset?
  [coll]

  (or
    (= (count coll) 0)
    (= (mod (multiset-exponent coll) 4) 0)))

(defn perfect-power-multiset?
  [coll]

  (and
    (multiset? coll)
    (not= (multiset-exponent coll) 1)))

(defn properly-divisible-multiset?
  [coll]

  (and
    (multiset? coll)
    (<= 2 (multiset-exponent coll))))

; Distinction relations
; these are essentially the properties which allow us
; to determine the different aspects of multisets.
(defn !=value
  [a b]

  (not= a b))

(defn !=multiset
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= a b)))

(defn !=multiset-exponent
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (multiset-exponent a)
          (multiset-exponent b))))

(defn !=multiset-distribution
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (dist a) (dist b))))

(defn !=multiset-support
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (support a) (support b))))

(defn !=multiset-support-partition
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (support-partition a) (support-partition b))))

(defn !=multiset-higher-signature
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (signature (signature a)) (signature (signature b)))))

(defn !=multiset-signature-support
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (set (signature a))
          (set (signature b)))))

(defn !=multiset-signature-order
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (multiset-order (signature a))
          (multiset-order (signature b)))))

(defn !=multiset-maximum-multiplicity
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (maximum-multiplicity a) (maximum-multiplicity b))))

(defn !=multiset-minimum-multiplicity
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (minimum-multiplicity a) (minimum-multiplicity b))))

(defn !=multiset-order
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (multiset-order a) (multiset-order b))))

(defn !=multiset-signature
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (signature a) (signature b))))

(defn !=multiset-cardinality
  [a b]

  (and
    (multiset? a)
    (multiset? b)
    (not= (count a) (count b))))

; Distance function
(defn set-distance
  [a b]

  (count (symmetric-difference a b)))

(defn multiset-distance
  [a b]

  (let [common-meet (meet-multisets a b)]
    (+ (count (multiset-difference a common-meet))
       (count (multiset-difference b common-meet)))))

; Partitionize a collection
(defn umap
  [func coll]

  (multiset (map func coll)))

(defn ufilter
  [func coll]

  (multiset (filter func coll)))

(defn pn
  "Partitionize any collection by an equivalence relation"
  [dependent? coll]

  (letfn [(independent? [a b]
            (not (dependent? a b)))
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
              (if (= (count new-dependents) 0)
                checked-elems
                (get-dependent-component
                  (difference unchecked-elems new-dependents)
                  (union checked-elems new-dependents)))))
          (get-dependent-components [coll]
            (if (= (count coll) 0)
              #{}
              (let [first-index (first coll)
                    current-component (get-dependent-component
                                        (difference coll #{first-index})
                                        #{first-index})]
                (union
                  #{current-component}
                  (get-dependent-components (difference coll current-component))))))]
    (let [keys-partition (get-dependent-components (support coll))]
      (set
        (map
          (fn [remaining-elements]
            (restrict-multiset coll remaining-elements))
          keys-partition)))))

(defn pn*
  [dependent? coll]

  (pn (complement dependent?) coll))

; Moore families
(defn moore-family
  [maximal-class closure]

  (assoc (Universal.
           (fn [coll]
             (and
               (or (not (set? coll))
                   (every? maximal-class coll))
               (equal-universals? coll (closure coll)))))
    :closure closure))

(defn cl
  [family subcoll]

  ((:closure family) subcoll))

; Intervals of sets
(defn logical-interval
  [lower-coll upper-coll]

  (if (seqable-universal? upper-coll)
    (set
      (map
        (partial union lower-coll)
        (power-set upper-coll)))
    (moore-family
      upper-coll
      (fn [coll]
        (union lower-coll coll)))))

; Visualize directed graphs as if they are unlabeled
(defn unlabel*
  [rel]

  (let [coll (vec (apply union (map set rel)))]
    (map
      (fn [[a b]]
        (list (.indexOf coll a) (.indexOf coll b)))
      rel)))

; Visualization
; isdirected determines rather or this is a directed or an undirected graph
; rankdir is a graphviz attribute that describes how the graph is layed out
; the clusters let you specify the clusters in the graph
; edges is a set of edges described as a set of ordered or unordered pairs
; islabeled is a boolean indicating rather or not labels are used
; labels is an association of vertex names to vertex labels
(defn output-graph!
  [code]

  (letfn [(get-file-name []
            (let [current-contents (file-seq (clojure.java.io/file "/tmp/"))
                  current-number (inc
                                   (count
                                     (filter
                                       (fn [coll]
                                         (.endsWith coll ".gv"))
                                       (map
                                         (fn [file]
                                           (.getName file))
                                         current-contents))))]
              (str "/tmp/tmp" current-number ".gv")))]
    (let [current-name (get-file-name)]
      (spit current-name code)
      (. (Runtime/getRuntime) exec (str "xdot " current-name)))))

(defn visualize-graphviz-file*
  [isdirected randkir clusters edges islabeled labels]

  (letfn [(replace-chars [string hash]
            (let [coll (set (keys hash))]
              (apply
                str
                (map
                  (fn [i]
                    (if (contains? coll i)
                      (get hash i)
                      i))
                  (seq string)))))
          (stringify [elem]
            (replace-chars
              (str
                \"
                (if (seq? elem)
                  (str (seq elem))
                  elem)
                \")
              {\% "\\%"}))
          (present-edge [edge]
            (if (universal? edge)
              (if (singular-universal? edge)
                (str (stringify (first edge)) " ; ")
                (let [[a b] (seq edge)]
                  (str (stringify a) " -- " (stringify b) " ; ")))
              (let [[a b] (seq edge)]
                (str (stringify a) " -> " (stringify b) " ; "))))
          (present-vertex [vertex]
            (str " " (stringify vertex) "; "))
          (present-labeled-vertex [index label]
            (str
              (stringify index)
              "[label=\"" label "\"];"))
          (present-cluster [index cluster]
            (str
              "subgraph cluster_" index "{ \n"
              (apply str (map present-vertex cluster))
              "\n}"))
          (present-clusters [clusters]
            (if (empty? clusters)
              ""
              (apply
                str
                (map-indexed
                  (fn [i v]
                    (present-cluster i v))
                  clusters))))]
    (output-graph!
      (str
        (if isdirected "digraph" "graph") " { \n"
        "rankdir = \"" randkir "\"; \n"
        (present-clusters clusters)
        (if islabeled
          (apply
            str
            (map-indexed
              (fn [i v]
                (present-labeled-vertex i v))
              labels))
          "")
        (apply str (map present-edge edges))
        "\n}"))))

; Specialized mechanisms for visualizing clustered directed graphs
(defn create-vertex-sequence-by-labeled-partition
  [coll]

  (apply
    concat
    (map
      (fn [key]
        (let [val (get coll key)]
          (map
            (fn [i]
              (list key i))
            val)))
      (keys coll))))

(defn create-clusters-by-vertex-sequence
  [to-index coll]

  (set
    (map
      (fn [key]
        (set
          (map
            (fn [val]
              (get to-index (list key val)))
            (get coll key))))
      (keys coll))))

(defn create-relation-by-vertex-sequence
  [to-index rel]

  (set
    (map
      (fn [pair]
        (map
          (fn [i]
            (get to-index i))
          pair))
      rel)))

(defn visualize-clustered-digraph*
  [rankdir partition edges]

  (let [vertex-sequence (create-vertex-sequence-by-labeled-partition partition)
        to-index (into
                   {}
                   (map-indexed
                     (fn [i v]
                       [v i])
                     vertex-sequence))
        clusters (create-clusters-by-vertex-sequence to-index partition)
        relation (create-relation-by-vertex-sequence to-index edges)]
    (visualize-graphviz-file*
      true
      rankdir
      clusters
      relation
      true
      (map second vertex-sequence))))

; A visualisation multimethod
(defmulti visualize type)

(defmethod visualize :default
  [rel]

  (let [isdirected (not (every? universal? rel))]
    (visualize-graphviz-file* isdirected "BT" #{} rel false [])))