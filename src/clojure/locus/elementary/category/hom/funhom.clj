(ns locus.elementary.category.hom.funhom
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.category.hom.sethom :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           (locus.elementary.diamond.core.object Diamond)))

; Let Sets^(->) be the topos of functions. Suppose that we have an ordered
; pair of functions (f,g). Then the hom class of (f,g) consists of all
; morphisms of functions from f to g. This file provides support for the
; enumeration of such morphisms of functions.

; We need some way of computing the extensions of a function
(defn extension-mappings
  "Enumerate function extensions on the level of mappings."
  [rel]

  (map
   (fn [i]
     (apply merge i))
   (apply
    cartesian-product
    (map (comp set (partial apply enumerate-mappings)) rel))))

(defn extension-bijections
  "Enumerate bijective extensions of specified functions."
  [rel]

  (map
   (fn [i]
     (apply merge i))
   (apply
    cartesian-product
    (map (comp set (partial apply enumerate-injective-mappings)) rel))))

; Hom class in the topos of functions
(defn function-morphisms
  [f g]

  (let [first-input (inputs f)
        first-output (inputs g)
        f-image (function-image f)
        second-input (difference (outputs f) f-image)
        second-output (outputs g)]
    (map
     (fn [[i o]]
       (Diamond.
        f
        g
        (SetFunction.
         first-input
         first-output
         i)
        (SetFunction.
         (outputs f)
         (outputs g)
         (fn [b]
           (if (contains? f-image b)
             (g (i (first (fiber f b))))
             (o b))))))
     (cartesian-product
      (set (enumerate-mappings first-input first-output))
      (set (enumerate-mappings second-input second-output))))))

; This deals with the enumeration of isomorphisms of functions
; by tackling the problem piece by piece.
(defn codomain-partitions
  [f g]

  (let [cardinalities (union
                       (set (fiber-cardinalities f))
                       (set (fiber-cardinalities g)))]
    (map
     (fn [cardinality]
       (list
        (set
         (filter
          (fn [i]
            (= (fiber-cardinality f i) cardinality))
          (outputs f)))
        (set
         (filter
          (fn [i]
            (= (fiber-cardinality g i) cardinality))
          (outputs g)))))
     (sort < cardinalities))))

(defn codomain-bijections
  [f g]

  (extension-bijections
   (codomain-partitions f g)))

(defn domain-partitions
  [f g output-mapping]

  (let [rel (seq output-mapping)]
    (map
     (fn [[k v]]
       [(fiber f k)
        (fiber g v)])
     rel)))

(defn domain-bijections
  [f g output-mapping]

  (extension-bijections
   (domain-partitions f g output-mapping)))

(defn function-isomappings
  [f g]

  (if (not= (fiber-cardinalities f) (fiber-cardinalities g))
    '()
    (mapcat
     (fn [output-mapping]
       (map
        (fn [input-mapping]
          (list input-mapping output-mapping))
        (domain-bijections f g output-mapping)))
     (codomain-bijections f g))))

(defn function-isomorphisms
  [f g]

  (if (not= (fiber-cardinalities f) (fiber-cardinalities g))
    '()
    (mapcat
     (fn [output-mapping]
       (map
        (fn [input-mapping]
          (Diamond.
           f
           g
           (SetFunction. (inputs f) (inputs g) input-mapping)
           (SetFunction. (outputs f) (outputs g) output-mapping)))
        (domain-bijections f g output-mapping)))
     (codomain-bijections f g))))

(defn number-of-function-isomorphisms
  [sig]

  (letfn [(factorial-product [coll]
            (apply * (map factorial coll)))]
    (* (factorial-product sig)
       (factorial-product (signature sig)))))

; Restricted subfunctions 
; We need to get all subfunctions of a given function in the topos of 
; functions with a given isomorphism type, in order to enumerate the
; elements of hom classes of the mono subcategory.
(defn remove-function-output
  [func x]

  (subfunction
   func
   (difference (inputs func) (fiber func x))
   (disj (outputs func) x)))

(defn remove-function-outputs
  [func coll]

  (subfunction
   func
   (difference (inputs func) (set-inverse-image func coll))
   (difference (outputs func) coll)))

(defn restricted-codomain-selections
  [func sig]

  (let [valid-cardinalities (set sig)
        out (outputs func)]
    (if (empty? out)
      (if (empty? sig)
        #{{}}
        #{})
      (let [first-output (first out)
            remaining-function (remove-function-output func first-output)]
        (union
         (apply
          union
          (map
           (fn [current-cardinality]
             (if (contains? valid-cardinalities current-cardinality)
               (let [remaining-multiset (remove-multiset-element sig current-cardinality)]
                 (set
                  (map
                   (fn [i]
                     (merge
                      {first-output current-cardinality}
                      i))
                   (restricted-codomain-selections remaining-function remaining-multiset))))
               #{}))
           (range (inc (fiber-cardinality func first-output)))))
         (restricted-codomain-selections remaining-function sig))))))

(defn subfunctions-by-codomain-selection
  [func sel]

  (map
   (fn [i]
     (list (apply union i) (set (keys sel))))
   (apply
    cartesian-product
    (map
     (fn [i]
       (selections (fiber func i) (sel i)))
     (keys sel)))))

(defn restricted-subfunctions
  [func sig]

  (mapcat
   (fn [sel]
     (subfunctions-by-codomain-selection func sel))
   (restricted-codomain-selections func sig)))

(defn restricted-function-subobjects
  [func sig]

  (mapcat
   (fn [sel]
     (map
      (fn [[i o]]
        (subfunction func i o))
      (subfunctions-by-codomain-selection func sel)))
   (restricted-codomain-selections func sig)))

; Attempt at enumerating injections to a given subalgebra
(defn selected-injections
  [source-function target-function target-in target-out]

  (map
   (fn [[in-f out-f]]
     (Diamond.
      source-function
      target-function
      (SetFunction. (inputs source-function) (inputs target-function) in-f)
      (SetFunction. (outputs source-function) (outputs target-function) out-f)))
   (function-isomappings
    source-function
    (subfunction target-function target-in target-out))))

(defn injective-function-hom
  [f g]

  (let [underlying-isomorphism-type (fiber-cardinalities f)]
    (mapcat
     (fn [[i o]]
       (selected-injections f g i o))
     (restricted-subfunctions g underlying-isomorphism-type))))

; We next need some technique of getting function congruences that
; are restricted to having a specific quotient isomorphism type.
(defn function-congruences-by-partition-selection
  [func sel]

  (let [output-partition (keys sel)]
    (map
     (fn [coll]
       (list
        (apply union coll)
        output-partition))
     (apply
      cartesian-product
      (for [part output-partition
            :when (not= (sel part) 0)]
        (restricted-set-partitions
         (set-inverse-image func part)
         (sel part)))))))

(defn enumerate-partition-selections
  [func sig]

  (let [coll (outputs func)
        possible-fiber-cardinalities (set sig)]
    (cond
      (and (empty? coll) (empty? sig)) '({})
      (< (count coll) (count sig)) '()
      :else (mapcat
             (fn [i]
               (mapcat
                (fn [cardinality]
                  (if (<= cardinality (count i))
                    (map
                     (fn [sel]
                       (merge sel {i cardinality}))
                     (enumerate-partition-selections
                      (remove-function-outputs func i)
                      (completely-remove-multiset-element sig cardinality)))
                    '()))
                possible-fiber-cardinalities))
             (disj (disj (power-set coll) #{}) coll)))))




