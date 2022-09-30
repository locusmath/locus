(ns locus.base.logic.numeric.natural
  (:require
    [locus.base.logic.core.set :refer :all]))

; Let Sets be the topos of sets, then the topos of finite sets is a subcategory of Sets. Every finite
; set can be associated to a natural number, which can also be considered a finite cardinal. This
; folder simply provides a range of utility functions and an ontology of finite cardinals. The ontology
; of finite cardinals divides non-negative integers into a partially ordered hierarchy of classes.

; Factors
(defn factors
  [num]

  (letfn [(prime-factors [n candidate acc]
            (cond
              (<= n 1) (reverse acc)
              (zero? (rem n candidate)) (recur (/ n candidate) candidate (cons candidate acc))
              :else (recur n (inc candidate) acc)))]
    (multiset (prime-factors num 2 '()))))

(def prime-signature
  (comp signature factors))

; Prime factorization
(defn prime-factorizations
  [& coll]

  (umap factors coll))

(defn exponent
  [num]

  (multiset-exponent (factors num)))

; Eulers totient function computed by prime factorisation
(defn eulers-totient-function
  [n]

  (apply
    *
    (let [prime-factorisation (factors n)]
      (map
        (fn [p]
          (let [k (multiplicity prime-factorisation p)]
            (* (int (Math/pow p k))
               (- 1 (/ 1 p)))))
        (support prime-factorisation)))))

; Polytope numbers
(defn polytope-number
  [n k]

  (if (<= k 1)
    (if (zero? k)
      1
      n)
    (/ (apply * (map (fn [i] (+ n i)) (range k)))
       (apply * (range 1 (inc k))))))

; Classification of natural numbers by prime signature
(defn prime-power?
  [num]

  (and
   (positive-integer? num)
   (<= (count (set (factors num))) 1)))

(defn prime-number?
  [num]

  (and
   (positive-integer? num)
   (= (count (set (factors num))) 1)))

(defn semiprime-number?
  [num]

  (and
   (positive-integer? num)
   (= 2 (count (factors num)))))

(defn composite-number?
  [num]

  (and
   (<= 4 num)
   (not (prime-number? num))))

(defn squarefree-number?
  [num]

  (universal? (factors num)))

(defn cubefree-number?
  [num]

  (max-multiplicity-two-multiset? (factors num)))

(defn square-number?
  [num]

  (== (Math/sqrt num) (int (Math/sqrt num))))

(defn cube-number?
  [num]

  (== (Math/pow num 1/3) (int (Math/pow num 1/3))))

(def prime-squared?
  (intersection
   square-number?
   prime-number?))

(def squarefree-semiprime-number?
  (intersection
   squarefree-number?
   semiprime-number?))

; Polynomial classes of natural numbers
(def even-natural-number?
  (intersection
   even?
   natural-number?))

(def odd-natural-number?
  (intersection
   odd?
   natural-number?))

(defn triangular-number?
  [num]

  (let [larger-num (inc (* 8 num))]
    (and
     (square-number? larger-num)
     (odd-natural-number? larger-num))))

; Exponential classes of natural numbers
(defn power-of-two?
  [num]

  (let [log-num (/ (Math/log num) (Math/log 2))]
    (== log-num (int log-num))))

(defn power-of-three?
  [num]

  (let [log-num (/ (Math/log num) (Math/log 3))]
    (== log-num (int log-num))))

(defn power-of-four?
  [num]

  (let [log-num (/ (Math/log num) (Math/log 4))]
    (== log-num (int log-num))))

; Ontology of perfect numbers
(defn sum-of-divisors
  [n]

  (apply + (divisors n)))

(defn perfect-number?
  [n]

  (= (* 2 n) (sum-of-divisors n)))

(defn deficient-number?
  [n]

  (< (sum-of-divisors n) (* 2 n)))

(defn abundant-number?
  [n]

  (< (* 2 n) (sum-of-divisors n)))


