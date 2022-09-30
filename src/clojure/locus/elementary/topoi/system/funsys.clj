(ns locus.elementary.topoi.system.funsys
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.difunction.core.funpair :refer :all]
            [locus.elementary.topoi.system.setrel :refer :all]
            [locus.elementary.topoi.system.partsys :refer :all]))

; Let Sets be the topos of sets. Then our support for set systems provides us with support
; for object systems of Sets. This file provides support for morphism systems of Sets.
; These are two dual objects that are necessary to provide better support for copresheaves,
; as every set valued functor targets sets of sets and functions. Given a general set
; valued functor, we can always produce a set of functions from its image. In another
; direction, given a family of functions we can produce a subcategory of Sets which
; naturally leads to an inclusion set valued functor.

; Compositional functionality for sets of functions
(defn compose-function-systems
  [system1 system2]

  (set
   (for [f system1
         g system2
         :when (= (inputs f) (outputs g))]
     (compose-functions f g))))

(defn function-system-power
  [system n]

  (if (= n 1)
    system
    (reduce compose-function-systems (repeat n system))))

; The function transitions family and its properties
(defn function-transitions
  [sys]

  (set (map underlying-transition sys)))

(defn inputs-family
  [sys]

  (set (map inputs sys)))

(defn outputs-family
  [sys]

  (set (map outputs sys)))

(defn kernels-family
  [sys]

  (set (map function-kernel sys)))

(defn images-family
  [sys]

  (map function-image sys))

; Special types of function systems
(defn family-inclusions
  [family]

  (let [coll (apply union family)]
    (set
     (map
      (fn [i]
        (inclusion-function i coll))
      family))))

(defn identities-family
  [family]

  (set (map identity-function family)))

; This produces a set of inclusion functions from a set system
(defn embedded-family-inclusions
  [family parent]

  (set
    (map
      (fn [coll]
        (inclusion-function coll parent))
      family)))

(defn embedded-images-family
  [sys]

  (set (map embedded-function-image sys)))

(defn get-embedded-family
  [sys]

  (embeddify-family (images-family sys)))

; Classes of function systems
; Function systems are the counterpart to set systems in the topos
; theoretic ontology of categorical set theory.
(def function-system?
  (power-set set-function?))

(def inclusions-family?
  (power-set set-function?))

(def identities-family?
  (power-set identity-function?))

; Cardinality classification
(defn singular-function-system?
  [sys]

  (and
    (function-system? sys)
    (= (count sys) 1)))

(defn size-two-function-system?
  [sys]

  (and
    (function-system? sys)
    (= (count sys) 2)))

(defn size-three-function-system?
  [sys]

  (and
    (function-system? sys)
    (= (count sys) 3)))

(defn size-four-function-system?
  [sys]

  (and
    (function-system? sys)
    (= (count sys) 4)))

; Function composition closure
(defn function-composition-closed?
  [system]

  (every?
   (fn [[a b]]
     (or
      (not (composable-functions? a b))
      (contains? system (compose-functions a b))))
   (cartesian-power system 2)))

(def identity-closed?
  (moore-family
    set-function?
    (fn [coll]
      (union
        coll
        (set
          (map
            identity-function
            (apply
              union
              (map
                (fn [i]
                  (set (list (inputs i) (outputs i))))
                coll))))))))

; Pair function systems
(defn pair-function-system
  [rel]

  (set
    (map
      (fn [[a b]]
        (pair-function a b))
      rel)))

(defn loop-function-system
  [coll]

  (set (map loop-function coll)))

(def pair-function-system?
  (power-set ordered-pair-function?))

(def loop-function-system?
  (power-set loop-function?))

(defn composition-closed-pair-function-system?
  [coll]

  (and
    (pair-function-system? coll)
    (transitive? (function-transitions coll))))

(defn categorical-pair-function-system?
  [coll]

  (and
    (pair-function-system? coll)
    (preorder? (function-transitions coll))))

; Classification of function systems by their member types
(def injective-function-system?
  (power-set injective?))

(def surjective-function-system?
  (power-set surjective?))

(def invertible-function-system?
  (power-set invertible?))

(def endofunctions-system?
  (power-set endofunction?))

(def autofunction-system?
  (power-set autofunction?))

; Parallel function systems
(defn parallel-function-system?
  [functions]

  (or
    (empty? functions)
    (apply = (map underlying-transition functions))))

(defn common-input-function-system?
  [functions]

  (or
    (empty? functions)
    (apply = (map inputs functions))))

(defn common-output-function-system?
  [functions]

  (or
    (empty? functions)
    (apply = (map outputs functions))))

(def parallel-endofunction-system?
  (intersection
    endofunctions-system?
    parallel-function-system?))

(def parallel-autofunction-system?
  (intersection
    autofunction-system?
    parallel-function-system?))

(def common-output-inclusions-family?
  (intersection
    common-output-function-system?
    inclusions-family?))

(def function-composition-closed-parallel-endofunction-system?
  (intersection
    parallel-endofunction-system?
    function-composition-closed?))

(def function-composition-closed-endofunction-system?
  (intersection
    endofunctions-system?
    function-composition-closed?))

(def function-composition-closed-parallel-autofunction-system?
  (intersection
    parallel-autofunction-system?
    function-composition-closed?))

(def function-composition-closed-autofunction-system?
  (intersection
    autofunction-system?
    function-composition-closed?))

; Projection systems
(defn projection-system?
  [sys]

  (and
    (common-input-function-system? sys)
    (product-partition-system? (kernels-family sys))))

(defn injection-system?
  [sys]

  (and
    (common-output-function-system? sys)
    (independent-family? (images-family sys))
    (or
      (empty? sys)
      (let [common-output (outputs (first sys))]
        (= common-output
           (apply union (images-family sys)))))))

; This in particular is applicable to set systems with a common target
(defn common-kernel
  [sys]

  (apply
    meet-set-partitions
    (map function-kernel sys)))

(defn common-image
  [sys]

  (apply
    union
    (map function-image sys)))

(defn together-injective-system?
  [sys]

  (and
    (common-input-function-system? sys)
    (unary-family? (common-kernel sys))))

(defn together-surjective-system?
  [sys]

  (and
    (common-output-function-system? sys)
    (or
      (empty? sys)
      (let [common-output (outputs (first sys))]
        (= (common-image sys)
           common-output)))))

(def together-surjective-inclusions-family?
  (intersection
    together-surjective-system?
    inclusions-family?))

(def together-injective-surjective-function-system?
  (intersection
    together-injective-system?
    surjective-function-system?))

(def element-function-system?
  (power-set element-function?))

; The inclusion ordering on a family of functions
(defn functional-inclusion-ordering
  [sys]

  (->SeqableRelation
    sys
    (fn [[a b]]
      (included-function? a b))
    {}))

; The common fiber and combined image of a function system
(defn common-fiber
  [sys x]

  (apply
    intersection
    (map
      (fn [func]
        (fiber func x))
      sys)))

(defn combined-image
  [sys coll]

  (apply
    union
    (map
      (fn [func]
        (set-image func coll))
      sys)))

; Restrict all functions in a system
(defn restrict-all
  [sys coll]

  (set
    (map
      (fn [func]
        (restrict-function func coll))
      sys)))

(defn family-of-element-functions
  [coll parent]

  (set
    (map
      (fn [i]
        (element-function i parent))
      coll)))


