(ns locus.elementary.difunction.core.funpair
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]))

; The topos of Sets^2 defines morphisms consisting of pairs of functions. This leads to a
; separate class for dealing with such morphisms of pairs of sets. This leads to an implementation
; distinction between disets and ordered pairs of sets, which are ordered collections. We
; provide support for both types of structure in our mathematical ontology.

; Relations between functions determined by their hom classes
(defn parallel-functions?
  [f g]

  (and
   (= (inputs f) (inputs g))
   (= (outputs f) (outputs g))))

(defn common-input-functions?
  [f g]

  (= (inputs f) (inputs g)))

(defn common-output-functions?
  [f g]

  (= (outputs f) (outputs g)))

(defn composable-functions?
  [f g]

  (= (outputs g) (inputs f)))

(defn symmetric-functions?
  [f g]

  (and
   (= (inputs f) (outputs g))
   (= (outputs g) (inputs f))))

(defn hom-independent-functions?
  [f g]

  (distinct?
   (inputs f)
   (outputs f)
   (inputs g)
   (outputs g)))

; Functions that meet on their common domain
(defn joinable-functions?
  [f g ]

  (let [common-domain (intersection (inputs f) (inputs g))]
    (every?
      (fn [x]
        (= (f x) (g x)))
      common-domain)))

; Inverse functions
(defn inverse-functions?
  [f g]

  (and
    (symmetric-functions? f g)
    (identity-function? (compose-functions f g))
    (identity-function? (compose-functions g f))))

; Relations between inclusion functions
(defn inclusion-function-pair?
  [f g]

  (and
   (inclusion-function? f)
   (inclusion-function? g)))

(defn common-output-inclusion-functions?
  [f g]

  (and
   (common-output-functions? f g)
   (inclusion-function? f)
   (inclusion-function? g)))

(defn disjoint-inclusions?
  [f g]

  (and
   (common-output-functions? f g)
   (inclusion-function? f)
   (inclusion-function? g)
   (empty? (intersection (function-image f) (function-image g)))))

(defn complementary-inclusions?
  [f g]

  (and
   (common-output-functions? f g)
   (inclusion-function? f)
   (inclusion-function? g)
   (and
    (empty? (intersection (function-image f) (function-image g)))
    (= (outputs f) (apply union (function-image f) (function-image g))))))


