(ns locus.simplicial.core.simplicial-morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]))

; We can use the data stored in instances of the SimplicialMorphism class to
; construct the simplex category. The data consists of a vector with two
; numbers as well as another composition vector element that defines the
; mapping of the simplicial morphism of finite ordinals.
(deftype SimplicialMorphism [source target data]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (set (range source)))
  (outputs [this] (set (range target)))

  clojure.lang.IFn
  (invoke [this arg]
    (nth data arg))
  (applyTo  [this args]
    (clojure.lang.AFn/applyToHelper this args))

  java.lang.Object
  (toString [this]
    (str source " -> " target " : " data)))

(defmethod print-method SimplicialMorphism [^SimplicialMorphism v ^java.io.Writer w]
  (.write w (.toString v)))

(defmethod compose* SimplicialMorphism
  [^SimplicialMorphism a, ^SimplicialMorphism b]

  (SimplicialMorphism.
    (source-object b)
    (target-object a)
    (compose-vectors (.data a) (.data b))))

(defn simplicial-identity-morphism
  [n]

  (SimplicialMorphism. n n (vec (range n))))

; Face and degeneracy maps of simplex categories
; The simplex category is characterized by the existence of certain generators:
; the face and degeneracy maps, which by factorisation can produce all
; morphisms of the category. This allows us to define simplicial sets by
; constructing presheaves over these generators.
(defn face-morphism
  [target-number forgetten-number]

  (SimplicialMorphism.
    (dec target-number)
    target-number
    (vec
      (map
        (fn [i]
          (if (<= forgetten-number i)
            (inc i)
            i))
        (range (dec target-number))))))

(defn degeneracy-morphism
  [target-number repeated-number]

  (SimplicialMorphism.
    (inc target-number)
    target-number
    (vec
      (map
        (fn [i]
          (if (< repeated-number i)
            (dec i)
            i))
        (range (inc target-number))))))

; Create a simplicial injection by forgetting a set of numbers
(defn simplicial-injection
  [n forgotten-numbers]

  (let [k (count forgotten-numbers)]
    (SimplicialMorphism.
      (- n k)
      n
      (vec
        (sort
          <=
          (difference (set (range n)) (set forgotten-numbers)))))))

(defn simplicial-injection-factorisation
  [n forgotten-numbers]

  (map-indexed
    (fn [i v]
      (face-morphism
        (- n i)
        (- v i)))
    (sort <= forgotten-numbers)))

(defn missing-numbers
  [simplicial-map]

  (difference (outputs simplicial-map) (function-image simplicial-map)))

; Simplicial equality lengths
(defn simplicial-equality-length
  [simplicial-map x]

  (loop [n 0
         i x]
    (let [currently-available (< (+ n x)
                                 (source-object simplicial-map))
          currently-equal (and
                            currently-available
                            (= (simplicial-map x)
                               (simplicial-map (+ n x))))]
      (if currently-equal
        (recur (inc n) (inc x))
        n))))

(defn simplicial-equality-lengths
  [simplicial-map]

  (let [n (source-object simplicial-map)]
    (loop [i 0
           rval []]
      (if (< i n)
        (let [next-length (simplicial-equality-length simplicial-map i)]
          (recur
            (+ i next-length)
            (conj rval next-length)))
        rval))))

(defn make-numeric-partition-by-composition
  [nums]

  (loop [i 0
         sum 0
         rval []]
    (if (<= (count nums) i)
      rval
      (recur
        (inc i)
        (+ sum (nth nums i))
        (conj rval (vec (range sum (+ sum (nth nums i)))))))))

(defn simplicial-kernel
  [simplicial-map]

  (make-numeric-partition-by-composition
    (simplicial-equality-lengths simplicial-map)))

; We can create a simplicial surjection by an additive composition
(defn simplicial-surjection
  [block-sizes]

  (let [t (count block-sizes)
        s (apply + block-sizes)]
    (SimplicialMorphism.
      s
      t
      (vec
        (mapcat
          (fn [i]
            (let [v (nth block-sizes i)]
              (repeat v i)))
          (range (count block-sizes)))))))

(defn simplicial-surjection-by-partition
  [partition]

  (simplicial-surjection (map count partition)))

(defn partition-component-pairs
  [component]

  (map
    (fn [i]
      (list (nth component i) (nth component (inc i))))
    (range (dec (count component)))))

(defn partition-pairs
  [partition]

  (mapcat
    (fn [component]
      (partition-component-pairs component))
    partition))

(defn simplicial-surjection-factorisation
  [partition]

  (let [pairs (partition-pairs partition)
        s (dec (apply + (map count partition)))]
    (reverse
      (map-indexed
       (fn [i v]
         (let [pair (nth pairs v)]
           (degeneracy-morphism
             (- s i)
             (first pair))))
       (range (dec (count pairs)) -1 -1)))))

; Factorise a morphism in the simplicial category first into epi and mono components
(defn simplicial-epi-mono-factorisation
  [simplicial-map]

  (list
    (simplicial-injection
      (target-object simplicial-map)
      (missing-numbers simplicial-map))
    (simplicial-surjection-by-partition (simplicial-kernel simplicial-map))))

; Factorise a morphism in the simplex category into all its fundamental face and
; degeneracy map components returning the full factorisation.
(defn full-simplicial-factorisation
  [simplicial-map]

  (concat
    (simplicial-injection-factorisation
      (target-object simplicial-map)
      (missing-numbers simplicial-map))
    (simplicial-surjection-factorisation (simplicial-kernel simplicial-map))))

; Ontology of simplicial morphisms
(defn simplicial-morphism?
  [x]

  (= (type x) SimplicialMorphism))

(defn injective-simplicial-morphism?
  [x]

  (and
    (simplicial-morphism? x)
    (distinct-seq? (seq (.data ^SimplicialMorphism x)))))

(defn surjective-simplicial-morphism?
  [x]

  (and
    (simplicial-morphism? x)
    (= (count (set (.data ^SimplicialMorphism x))) (target-object x))))

(defn face-morphism?
  [x]

  (and
    (injective-simplicial-morphism? x)
    (= (inc (source-object x)) (target-object x))))

(defn degeneracy-morphism?
  [x]

  (and
    (surjective-simplicial-morphism? x)
    (= (inc (target-object x)) (source-object x))))

(defn simplicial-endomorphism?
  [x]

  (and
    (simplicial-morphism? x)
    (= (source-object x) (target-object x))))

(defn simplicial-identity-morphism?
  [x]

  (and
    (simplicial-morphism? x)
    (= (source-object x) (target-object x))
    (let [data (.data ^SimplicialMorphism x)
          n (count data)]
      (every?
        (fn [i]
          (= (nth data i) i))
        (range n)))))

; Test for simplicial morphisms which need to satisfy a number of conditions
; including that they have proper source and target numbers, as well as
; valid data that constitutes a monotone map.
(defn valid-simplicial-morphism?
  [morphism]

  (let [source-number (source-object morphism)
        target-number (target-object morphism)
        data (.data morphism)]
    (and
      ; the source and target objects of a simplicial morphism are positive integers
      ; which represent the order type of a finite total order
      (positive-integer? source-number)
      (positive-integer? target-number)

      ; the mapping data of the simplicial morphism is a vector
      (vector? data)

      ; test that the mapping data corresponds to the input number
      (= (count data) source-number)

      ; test that all outputs are contained in the output ordinal
      (let [max-number (dec target-number)]
        (every?
          (fn [i]
            (<= i max-number))
          data))

      ; finally test if the simplicial morphism is monotone
      (every?
        (fn [i]
          (or
            (zero? i)
            (let [current-value (nth data i)
                  previous-value (nth data (dec i))]
              (<= previous-value current-value))))
        (range (count data))))))









