(ns locus.elementary.topoi.copresheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.base.effects.global.identity :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.generated-category :refer :all]
            [locus.algebra.groupoid.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.quiver.diset.core.morphism :refer :all]
            [locus.quiver.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.bijection.core.morphism :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.elementary.incidence.core.object :refer :all]
            [locus.elementary.triangle.core.object :refer :all]
            [locus.elementary.dependency.core.object :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.action.global.morphism :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.quiver.permutable.morphism :refer :all]
            [locus.elementary.quiver.dependency.morphism :refer :all]
            [locus.quiver.ternary.core.object :refer :all]
            [locus.quiver.ternary.core.morphism :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all]
            [locus.elementary.two-quiver.globular.object :refer :all]
            [locus.elementary.galois.copresheaf.object :refer :all]
            [locus.quiver.nary.core.object :refer :all]
            [locus.quiver.nary.core.morphism :refer :all])
  (:import (locus.quiver.binary.core.morphism MorphismOfQuivers)
           (locus.elementary.quiver.permutable.morphism MorphismOfPermutableQuivers)
           (locus.elementary.quiver.unital.morphism MorphismOfUnitalQuivers)
           (locus.elementary.quiver.dependency.morphism MorphismOfDependencyQuivers)
           (locus.elementary.action.global.object MSet)
           (locus.elementary.action.global.morphism EquivariantMap)
           (locus.quiver.ternary.core.morphism MorphismOfTernaryQuivers)
           (locus.elementary.two_quiver.core.object TwoQuiver)
           (locus.elementary.two_quiver.globular.object TwoGlobularSet)
           (locus.elementary.two_quiver.path.object PathQuiver)
           (locus.base.function.core.object SetFunction)
           (locus.elementary.triangle.core.object SetTriangle)
           (locus.algebra.category.core.morphism Functor)
           (locus.order.lattice.core.object Lattice)
           (locus.elementary.galois.copresheaf.object GaloisCopresheaf)
           (locus.quiver.nary.core.object NaryQuiver)))

; Copresheaves
; A copresheaf is a set-valued functor and therefore an object of a topos Sets^(C). These are the
; primary  objects of study in Locus. Using presheaf theoretic foundations, we model sets as
; presheaves over a  single object and functions as presheaves over an ordered pair, and study
; different models of  related structures defined by presheaves using the methods of topos theory.
(deftype Copresheaf [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] sets)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

; Component parts of copresheaves
(defmethod get-set Copresheaf
  [copresheaf x]

  (object-apply copresheaf x))

(defmethod get-function Copresheaf
  [copresheaf x]

  (morphism-apply copresheaf x))

; All sets and functions of copresheaves
(defn all-sets
  [copresheaf]

  (set
    (map
      (partial get-set copresheaf)
      (objects (index copresheaf)))))

(defn all-functions
  [copresheaf]

  (set
    (map
      (partial get-function copresheaf)
      (morphisms (index copresheaf)))))

; Index categories
(defmethod index Copresheaf
  [^Copresheaf copresheaf] (.-category copresheaf))

; Index categories for galois copresheaves
(def galois-index-category
  (adjoin-composition
    (create-unital-quiver
      {0 0
       1 1}
      {2 [0 1]
       3 [1 0]
       4 [0 0]
       5 [1 1]})
    (fn [[a b]]
      (letfn [(identity-arrow? [x]
                (or (= x 0) (= x 1)))]
        (cond
          (identity-arrow? a) b
          (identity-arrow? b) a
          (= a b 4) 4
          (= a b 5) 5
          (and (= a 3) (= b 2)) 4
          (and (= a 2) (= b 3)) 5
          (and (= a 2) (= b 4)) 2
          (and (= a 3) (= b 5)) 3)))))

(defmethod index GaloisCopresheaf
  [^GaloisCopresheaf copresheaf] galois-index-category)

; Nary quivers as copresheaves
(defmethod index NaryQuiver
  [nary-quiver]

  (n-arrow-category (quiver-arity nary-quiver)))

; Index categories for quivers
(def t2
  (thin-category (total-order 0 1)))

(def t2*
  (adjoin-generators
    (simple-labeled-category
      #{0 1}
      {0 [0 0]
       1 [1 1]
       2 [0 1]
       3 [0 1]})
    '#{2, 3}))

(defmethod index :locus.quiver.binary.core.object/quiver
  [quiver] t2*)

(defmethod index MorphismOfQuivers
  [morphism] (category-product t2 t2*))

; Index categories for permutable quivers
(def permutable-quiver-index-category
  (adjoin-generators
    (adjoin-composition
     (create-unital-quiver
       {0 0
        1 1}
       {2 [0 1]
        3 [0 1]
        4 [0 0]})
     (fn [[a b]]
       (let [source-arrow 2
             target-arrow 3
             reverse-arrow 4]
         (letfn [(identity-arrow? [x]
                   (or (= x 0) (= x 1)))]
           (cond
             (identity-arrow? a) b
             (identity-arrow? b) a
             (and (= a source-arrow) (= b reverse-arrow)) target-arrow
             (and (= a target-arrow) (= b reverse-arrow)) source-arrow
             (and (= a reverse-arrow) (= b reverse-arrow)) 0)))))
    '#{2,3,4}))

(defmethod index :locus.elementary.quiver.permutable.object/permutable-quiver
  [quiver] permutable-quiver-index-category)

(defmethod index MorphismOfPermutableQuivers
  [quiver] (category-product (thin-category t2 permutable-quiver-index-category)))

; Index categories for unital quivers
(def unital-quiver-index-category
  (adjoin-generators
    (adjoin-composition
     (create-unital-quiver
       {0 0
        1 1}
       {2 [0 1]
        3 [0 1]
        4 [1 0]
        5 [0 0]
        6 [0 0]})
     (fn [[a b]]
       (let [morphic-identity 0
             object-identity 1
             source-arrow 2
             target-arrow 3
             identity-arrow 4
             source-identity-arrow 5
             target-identity-arrow 6]
         (letfn [(identity-arrow? [x]
                   (or (= x morphic-identity) (= x object-identity)))
                 (component-function? [x]
                   (or (= x source-arrow) (= x target-arrow)))
                 (component-identity? [x]
                   (or (= x source-identity-arrow) (= x target-identity-arrow)))]
           (cond
             (identity-arrow? a) b
             (identity-arrow? b) a
             (and (component-identity? a) (component-identity? b)) b
             (and (component-function? a) (= b source-identity-arrow)) source-arrow
             (and (component-function? a) (= b target-identity-arrow)) target-arrow
             (and (component-identity? a) (= b identity-arrow)) identity-arrow
             (and (component-function? a) (= b identity-arrow)) object-identity
             (and (= a identity-arrow) (= b source-arrow)) source-identity-arrow
             (and (= a identity-arrow) (= b target-arrow)) target-identity-arrow)))))
    '#{2 3 4}))

(defmethod index :locus.elementary.quiver.unital.object/unital-quiver
  [unital-quiver] unital-quiver-index-category)

(defmethod index MorphismOfUnitalQuivers
  [morphism] (category-product t2 unital-quiver-index-category))

; Index categories for dependency quivers
(def dependency-quiver-index-category
  (adjoin-generators
    (adjoin-composition
     (create-unital-quiver
       {0 0
        1 1}
       {2 [0 1]
        3 [0 1]
        4 [1 0]
        5 [0 0]
        6 [0 0]
        7 [0 0]})
     (fn [[a b]]
       (let [morphic-identity 0
             object-identity 1
             source-arrow 2
             target-arrow 3
             identity-arrow 4
             source-identity-arrow 5
             target-identity-arrow 6
             reverse-arrow 7]
         (letfn [(identity-arrow? [x]
                   (or (= x morphic-identity) (= x object-identity)))
                 (unital-quiver-arrow? [x]
                   (contains? #{0 1 2 3 4 5 6} x))]
           (cond
             (identity-arrow? a) b
             (identity-arrow? b) a
             (and
               (unital-quiver-arrow? a)
               (unital-quiver-arrow? b)) (unital-quiver-index-category (list a b))

             (and (= a source-arrow) (= b reverse-arrow)) target-arrow
             (and (= a target-arrow) (= b reverse-arrow)) source-arrow
             (and (= a reverse-arrow) (= b reverse-arrow)) morphic-identity

             (and (= a reverse-arrow) (= b identity-arrow)) identity-arrow
             (and (= a reverse-arrow) (= b source-identity-arrow)) source-identity-arrow
             (and (= a reverse-arrow) (= b target-identity-arrow)) target-identity-arrow
             (and (= a source-identity-arrow) (= b reverse-arrow)) target-identity-arrow
             (and (= a target-identity-arrow) (= b reverse-arrow)) source-identity-arrow)))))
    '#{2 3 4 7}))

(defmethod index :locus.elementary.quiver.dependency.object/dependency-quiver
  [quiver] dependency-quiver-index-category)

(defmethod index MorphismOfDependencyQuivers
  [morphism] (category-product t2 dependency-quiver-index-category))

; Index categories for monoid actions
(defmethod index MSet
  [^MSet mset] (.-monoid mset))

(defmethod index EquivariantMap
  [morphism] (category-product t2 (index (source-object morphism))))

; Index categories for ternary quivers
(def t3*
  (adjoin-generators
    (simple-labeled-category
      #{0 1}
      {0 [0 0]
       1 [1 1]
       2 [0 1]
       3 [0 1]
       4 [0 1]})
    '#{2, 3, 4}))

(defmethod index :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [ternary-quiver] t3*)

(defmethod index MorphismOfTernaryQuivers
  [morphism] (product t2 t3*))

; Globular set theory
(defn n-globular-set-index-category
  [arg]

  (let [n (inc arg)]
    (->Category
      (->UnitalQuiver
        (apply
          union
          (set
            (map
              (fn [i]
                (apply
                  union
                  (set
                    (map
                      (fn [j]
                        (if (= i j)
                          #{(list i j 0)}
                          #{(list i j 0) (list i j 1)}))
                      (range (inc i))))))
              (range n))))
        (->Upto n)
        first
        second
        (fn [n]
          (list n n 0)))
      (fn [[[a1 a2 a3] [b1 b2 b3]]]
        (cond
          (= a1 a2) (list b1 b2 b3)
          (= b1 b2) (list a1 a2 a3)
          :else (list b1 a2 a3))))))

(def two-globular-set-index-category
  (n-globular-set-index-category 2))

; Enumerate all binary based pairs of n edges in an n quiver
(defn enumerate-n-edges
  [i j]

  (let [n (- i j)]
    (map
      (fn [binary-sequence]
        (list i j binary-sequence))
      (apply cartesian-product (repeat n #{0 1})))))

(defn enumerate-n-edges-starting-from-index
  [i]

  (apply
    union
    (map
      (fn [j]
        (set (enumerate-n-edges i j)))
      (range (inc i)))))

(defn enumerate-all-n-edges
  [i]

  (apply
    union
    (map
      (fn [j]
        (enumerate-n-edges-starting-from-index j))
      (range (inc i)))))

(defn n-quiver-index-category
  [n]

  (->Category
    (->UnitalQuiver
      (enumerate-all-n-edges n)
      (set (range (inc n)))
      first
      second
      (fn [n]
        (list n n '())))
    (fn [[a b]]
      (list
        (first b)
        (second a)
        (concat (nth a 2) (nth b 2))))))

(def two-quiver-index-category
  (n-quiver-index-category 2))

; Path quivers
(def path-quiver-index-category
  (adjoin-composition
    (create-unital-quiver
      {2 '(2 2 0)
       1 '(1 1 0)
       0 '(0 0 0)}
      '{(1 0 0) (1 0)
        (1 0 1) (1 0)
        (2 1 0) (2 1)
        (2 1 1) (2 1)
        (2 0 0) (2 0)
        (2 0 1) (2 0)
        (2 0 2) (2 0)})
    (fn [[a b]]
      (letfn [(identity-arrow? [[a b c]]
                (= a b))]
        (let [one-source '(1 0 0)
              two-source '(2 1 0)
              two-middle '(2 0 1)
              one-target '(1 0 1)
              two-target '(2 1 1)
              two-last '(2 0 2)
              two-front '(2 0 0)]
          (cond
           (identity-arrow? a) b
           (identity-arrow? b) a
           (and (= a one-source) (= b two-source)) two-middle
           (and (= a one-target) (= b two-source)) two-last
           (and (= a one-source) (= b two-target)) two-front
           (and (= a one-target) (= b two-target)) two-middle))))))

; Index categories for two quivers
(defmethod index TwoQuiver
  [two-quiver] two-quiver-index-category)

(defmethod index TwoGlobularSet
  [two-globular-set] two-globular-set-index-category)

(defmethod index PathQuiver
  [path-quiver] path-quiver-index-category)

; The different composition diamond index category
; This is like a diamond, except that the two different paths along the diamond produce different
; compositions. This results in a different index category for copresheaves.
(def different-composition-diamond
  (adjoin-composition
    (create-unital-quiver
      {0 '(0 0)
       1 '(1 1)
       2 '(2 2)
       3 '(3 3)}
      {'(0 1)   [0 1]
       '(0 2)   [0 2]
       '(1 3)   [1 3]
       '(2 3)   [2 3]
       '(0 1 3) [0 3]
       '(0 2 3) [0 3]})
    (fn [[[c d] [a b]]]
      (cond
        (= a b) (list c d)
        (= c d) (list a b)
        :else (list a b d)))))

; An ordinary quiver can be considered to be a special case of a binary quiver, while there are
; many other forms of quivers beyond those, and each of them has their own index category.
; These index categories consist of two objects and a collection of morphisms between
; them that indicate the vertex value of an edge at each of its component indices.
(defn nary-quiver-category
  [n]

  (simple-labeled-category
    #{"edges" "vertices"}
    (into
      {}
      (concat
        (list
          ["1ₑ" ["edges" "edges"]]
          ["1ᵥ" ["vertices" "vertices"]])
        (map
          (fn [i]
            [i ["edges" "vertices"]])
          (range n))))))

; Functional quivers:
; We can define functional quivers by adjoining a function to a quiver that targets its edge set.
; The function could be of any sort, and so this is one of the first steps beyond elementary
; quivers in presheaf theory.
(def functional-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"paths"    "1ₚ"
         "edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"   ["edges" "vertices"]
         "target"   ["edges" "vertices"]
         "∘"        ["paths" "edges"]
         "∘ source" ["paths" "vertices"]
         "∘ target" ["paths" "vertices"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (or (= x "1ₚ") (= x "1ₑ") (= x "1ᵥ")))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and (= a "source") (= b "∘")) "∘ source"
            (and (= a "target") (= b "∘")) "∘ target"))))
    '#{"source" "target" "∘"}))

(def functional-unital-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"paths"    "1ₚ"
         "edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"   ["edges" "vertices"]
         "target"   ["edges" "vertices"]

         "identity" ["vertices" "edges"]
         "idt"      ["edges" "edges"]
         "ids"      ["edges" "edges"]

         "∘"        ["paths" "edges"]
         "∘ source" ["paths" "vertices"]
         "∘ target" ["paths" "vertices"]

         "∘ idt"    ["paths" "edges"]
         "∘ ids"    ["paths" "edges"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ"} x))
                (unital-quiver-arrow? [x]
                  (contains? #{"1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids"} x))
                (functional-quiver-arrow? [x]
                  (contains? #{"1ₑ" "1ᵥ" "source" "target" "∘" "∘ source" "∘ target"} x))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and
              (unital-quiver-arrow? a)
              (unital-quiver-arrow? b)) (unital-quiver-index-category (list a b))
            (and
              (functional-quiver-arrow? a)
              (functional-quiver-arrow? b)) (functional-quiver-index-category (list a b))
            (and
              (= a "idt") (= b "∘")) "∘ idt"
            (and
              (= a "ids") (= b "∘")) "∘ ids"
            (and
              (= a "identity") (= b "∘ source")) "∘ ids"
            (and
              (= a "identity") (= b "∘ target")) "∘ idt"

            (and (= a "source") (= b "∘ ids")) "∘ source"
            (and (= a "target") (= b "∘ ids")) "∘ source"
            (and (= a "ids") (= b "∘ ids")) "∘ ids"
            (and (= a "idt") (= b "∘ ids")) "∘ ids"

            (and (= a "source") (= b "∘ idt")) "∘ target"
            (and (= a "target") (= b "∘ idt")) "∘ target"
            (and (= a "ids") (= b "∘ idt")) "∘ idt"
            (and (= a "idt") (= b "∘ idt")) "∘ idt"))))
    '#{"source" "target" "∘" "identity"}))

(def functional-dependency-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"paths"    "1ₚ"
         "edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"    ["edges" "vertices"]
         "target"    ["edges" "vertices"]

         "identity"  ["vertices" "edges"]
         "idt"       ["edges" "edges"]
         "ids"       ["edges" "edges"]

         "∘"         ["paths" "edges"]
         "∘ source"  ["paths" "vertices"]
         "∘ target"  ["paths" "vertices"]

         "∘ idt"     ["paths" "edges"]
         "∘ ids"     ["paths" "edges"]

         "reverse"   ["edges" "edges"]
         "∘ reverse" ["paths" "edges"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ"} x))
                (dependency-quiver-arrow? [x]
                  (contains? #{"1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids" "reverse"} x))
                (functional-unital-quiver-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids"
                               "∘" "∘ source" "∘ target" "∘ ids" "∘ idt"} x))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and
              (dependency-quiver-arrow? a)
              (dependency-quiver-arrow? b)) (dependency-quiver-index-category (list a b))
            (and
              (functional-unital-quiver-arrow? a)
              (functional-unital-quiver-arrow? b)) (functional-unital-quiver-index-category (list a b))

            (and (= a "reverse") (= b "∘")) "∘ reverse"
            (and (= a "reverse") (= b "∘ ids")) "∘ ids"
            (and (= a "reverse") (= b "∘ idt")) "∘ idt"

            (and (= a "reverse") (= b "∘ reverse")) "∘"
            (and (= a "source") (= b "∘ reverse")) "∘ target"
            (and (= a "target") (= b "∘ reverse")) "∘ source"
            (and (= a "ids") (= b "∘ reverse")) "∘ idt"
            (and (= a "idt") (= b "∘ reverse")) "∘ ids"))))
    '#{"source" "target" "∘" "identity" "reverse"}))

; Compositional quivers:
; These are defined by combining a ternary quiver with a binary quiver, so that
; the ternary compositional quiver has as its objects the morphisms of the other
; binary quiver. These are an alternative presheaf theoretic model for elementary categories.
(def compositional-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"paths"    "1ₚ"
         "edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"   ["edges" "vertices"]
         "target"   ["edges" "vertices"]
         "first"    ["paths" "edges"]
         "second"   ["paths" "edges"]
         "∘"        ["paths" "edges"]
         "cm"   ["paths" "vertices"]
         "cs" ["paths" "vertices"]
         "ct" ["paths" "vertices"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (or (= x "1ₚ") (= x "1ₑ") (= x "1ᵥ")))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and (= a "source") (= b "∘")) "cs"
            (and (= a "target") (= b "∘")) "ct"
            (and (= a "source") (= b "first")) "cm"
            (and (= a "source") (= b "second")) "cs"
            (and (= a "target") (= b "first")) "ct"
            (and (= a "target") (= b "second")) "cm"))))
    #{"source" "target" "first" "second" "∘"}))

(def compositional-unital-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"paths"    "1ₚ"
         "edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"   ["edges" "vertices"]
         "target"   ["edges" "vertices"]
         "first"    ["paths" "edges"]
         "second"   ["paths" "edges"]
         "∘"        ["paths" "edges"]
         "cm"       ["paths" "vertices"]
         "cs"       ["paths" "vertices"]
         "ct"       ["paths" "vertices"]

         "identity" ["vertices" "edges"]
         "idt"      ["edges" "edges"]
         "ids"      ["edges" "edges"]

         "idcm"     ["paths" "edges"]
         "idcs"     ["paths" "edges"]
         "idct"     ["paths" "edges"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ"} x))
                (unital-quiver-arrow? [x]
                  (contains? #{"1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids"} x))
                (compositional-quiver-arrow? [x]
                  (contains? #{"source" "target" "first" "second" "∘" "cm" "cs" "ct"} x))
                (morphic-identity-arrow? [x]
                  (contains? #{"ids" "idt"} x))
                (path-identity-arrow? [x]
                  (contains? #{"idcm" "idcs" "idct"} x))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and
              (compositional-quiver-arrow? a)
              (compositional-quiver-arrow? b)) (compositional-quiver-index-category (list a b))
            (and
              (unital-quiver-arrow? a)
              (unital-quiver-arrow? b)) (unital-quiver-index-category (list a b))
            (and (= a "ids") (= b "first"))
            (and (= a "idt") (= b "first"))

            (and (= a "ids") (= b "∘")) "idcs"
            (and (= a "idt") (= b "∘")) "idct"
            (and (= a "ids") (= b "first")) "idcm"
            (and (= a "ids") (= b "second")) "idcs"
            (and (= a "idt") (= b "first")) "idct"
            (and (= a "idt") (= b "second")) "idcm"
            (and (= a "identity") (= b "cm")) "idcm"
            (and (= a "identity") (= b "cs")) "idcs"
            (and (= a "identity") (= b "ct")) "idct"
            (and (or (= a "source") (= a "target")) (= b "idcs")) "cs"
            (and (or (= a "source") (= a "target")) (= b "idct")) "ct"
            (and (or (= a "source") (= a "target")) (= b "idcm")) "cm"
            (and (morphic-identity-arrow? a) (path-identity-arrow? b)) b))))
    #{"source" "target" "first" "second" "∘" "identity"}))

(def compositional-dependency-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"paths"    "1ₚ"
         "edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"         ["edges" "vertices"]
         "target"         ["edges" "vertices"]
         "first"          ["paths" "edges"]
         "second"         ["paths" "edges"]
         "∘"              ["paths" "edges"]
         "cm"             ["paths" "vertices"]
         "cs"             ["paths" "vertices"]
         "ct"             ["paths" "vertices"]

         "identity"       ["vertices" "edges"]
         "idt"            ["edges" "edges"]
         "ids"            ["edges" "edges"]

         "idcm"           ["paths" "edges"]
         "idcs"           ["paths" "edges"]
         "idct"           ["paths" "edges"]

         "reverse"        ["edges" "edges"]
         "∘ reverse"      ["paths" "edges"]
         "first reverse"  ["paths" "edges"]
         "second reverse" ["paths" "edges"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ"} x))
                (dependency-quiver-arrow? [x]
                  (contains? #{"1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids" "reverse"} x))
                (compositional-unital-quiver-arrow? [x]
                  (contains?
                    #{"ct" "idct" "idcs" "second" "∘" "ids" "1ᵥ" "identity"
                      "idcm" "1ₑ" "source" "1ₚ" "target" "cs" "idt" "cm" "first"}
                    x))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and (dependency-quiver-arrow? a)
                 (dependency-quiver-arrow? b)) (dependency-quiver-index-category (list a b))
            (and (compositional-unital-quiver-arrow? a)
                 (compositional-unital-quiver-arrow? b)) (compositional-unital-quiver-index-category
                                                           (list a b))
            (and (= a "source") (= b "∘ reverse")) "ct"
            (and (= a "target") (= b "∘ reverse")) "cs"
            (and (= a "source") (= b "first reverse")) "ct"
            (and (= a "target") (= b "first reverse")) "cm"
            (and (= a "source") (= b "second reverse")) "cm"
            (and (= a "target") (= b "second reverse")) "cs"
            (and (= a "ids") (= b "∘ reverse")) "idct"
            (and (= a "idt") (= b "∘ reverse")) "idcs"
            (and (= a "ids") (= b "first reverse")) "idct"
            (and (= a "idt") (= b "first reverse")) "idcm"
            (and (= a "ids") (= b "second reverse")) "idcm"
            (and (= a "ids") (= b "second reverse")) "idcs"
            (and (= a "reverse") (= b "first")) "first reverse"
            (and (= a "reverse") (= b "second")) "second reverse"
            (and (= a "reverse") (= b "∘")) "∘ reverse"
            (and (= a "reverse") (= b "idcm")) "idcm"
            (and (= a "reverse") (= b "idcs")) "idcs"
            (and (= a "reverse") (= b "idct")) "idct"
            (and (= a "reverse") (= b "first reverse")) "first"
            (and (= a "reverse") (= b "second reverse")) "second"
            (and (= a "reverse") (= b "∘ reverse")) "∘"))))
    #{"source" "target" "first" "second" "∘" "identity" "reverse"}))

; Index categories for categories themselves defined as objects in the topos of compositional quivers
(defmethod index :locus.elementary.copresheaf.core.protocols/partial-magmoid
  [obj] compositional-quiver-index-category)

(defmethod index :locus.elementary.copresheaf.core.protocols/category
  [obj] compositional-unital-quiver-index-category)

(defmethod index :locus.elementary.copresheaf.core.protocols/groupoid
  [groupoid] compositional-dependency-quiver-index-category)

; Every morphism in a topos of copresheaves corresponds to a copresheaf
(defn create-copresheaf-by-morphism
  [source target func]

  (let [index-category (index source)
        double-index-category (product t2 index-category)]
    (Copresheaf.
      double-index-category
      (fn [[i v]]
        (case i
          0 (object-apply source v)
          1 (object-apply target v)))
      (fn [[[i j] v]]
        (case [i j]
          [0 0] (morphism-apply source v)
          [1 1] (morphism-apply target v)
          [0 1] (compose
              (morphism-apply target v)
              (func (source-element index-category v))))))))

; Convert things into copresheaves
(defmulti to-copresheaf type)

(defmethod to-copresheaf :default
  [obj]

  (let [cat (index obj)]
    (if (nil? cat)
      (throw (new IllegalArgumentException))
      (->Copresheaf
        cat
        (partial get-set obj)
        (partial get-function obj)))))

; First and second projection functions on composability of a quiver
(defn composability-first-function
  [quiver]

  (->SetFunction
    (composability-relation quiver)
    (morphisms quiver)
    first))

(defn composability-second-function
  [quiver]

  (->SetFunction
    (composability-relation quiver)
    (morphisms quiver)
    second))

; This is where we implement the presheaf theory of categories
(defn make-compositional-quiver
  [category]

  (Copresheaf.
    compositional-quiver-index-category
    (fn [obj]
      (case obj
        "vertices" (objects category)
        "edges" (morphisms category)
        "paths" (inputs category)))
    (fn [arrow]
      (case arrow
        "1ₚ" (identity-function (inputs category))
        "1ₑ" (identity-function (morphisms category))
        "1ᵥ" (identity-function (objects category))
        "source" (source-function category)
        "target" (target-function category)
        "first" (composability-first-function category)
        "second" (composability-second-function category)
        "∘" (underlying-function category)
        "cm" (compose (source-function category) (composability-first-function category))
        "cs" (compose (source-function category) (composability-second-function category))
        "ct" (compose (target-function category) (composability-first-function category))))))

(defn make-compositional-unital-quiver
  [category]

  (Copresheaf.
    compositional-unital-quiver-index-category
    (fn [obj]
      (case obj
        "vertices" (objects category)
        "edges" (morphisms category)
        "paths" (inputs category)))
    (fn [arrow]
      (case arrow
        "1ₚ" (identity-function (inputs category))
        "1ₑ" (identity-function (morphisms category))
        "1ᵥ" (identity-function (objects category))
        "source" (source-function category)
        "target" (target-function category)
        "first" (composability-first-function category)
        "second" (composability-second-function category)
        "∘" (underlying-function category)
        "cm" (compose (source-function category) (composability-first-function category))
        "cs" (compose (source-function category) (composability-second-function category))
        "ct" (compose (target-function category) (composability-first-function category))
        "identity" (identity-element-function category)
        "idt" (source-identity-function category)
        "ids" (target-identity-function category)
        "idct" (compose (target-identity-function category) (underlying-function category))
        "idcs" (compose (source-identity-function category) (underlying-function category))
        "idcm" (identity-function
                 (compose
                   (source-function category)
                   (composability-first-function category)))))))

(defn make-compositional-dependency-quiver
  [category]

  (Copresheaf.
    compositional-dependency-quiver-index-category
    (fn [obj]
      (case obj
        "vertices" (objects category)
        "edges" (morphisms category)
        "paths" (inputs category)))
    (fn [arrow]
      (case arrow
        "1ₚ" (identity-function (inputs category))
        "1ₑ" (identity-function (morphisms category))
        "1ᵥ" (identity-function (objects category))
        "source" (source-function category)
        "target" (target-function category)
        "first" (composability-first-function category)
        "second" (composability-second-function category)
        "∘" (underlying-function category)
        "cm" (compose (source-function category) (composability-first-function category))
        "cs" (compose (source-function category) (composability-second-function category))
        "ct" (compose (target-function category) (composability-first-function category))
        "identity" (identity-element-function category)
        "idt" (source-identity-function category)
        "ids" (target-identity-function category)
        "idct" (compose (target-identity-function category) (underlying-function category))
        "idcs" (compose (source-identity-function category) (underlying-function category))
        "idcm" (identity-function
                 (compose
                   (source-function category)
                   (composability-first-function category)))
        "reverse" (inverse-function category)
        "∘ reverse" (compose (inverse-function category) (underlying-function category))
        "first reverse" (compose (inverse-function category) (composability-first-function category))
        "second reverse" (compose (inverse-function category) (composability-second-function category))))))

(defmethod to-copresheaf :locus.elementary.copresheaf.core.protocols/semigroupoid
  [semigroupoid] (make-compositional-quiver semigroupoid))

(defmethod to-copresheaf :locus.elementary.copresheaf.core.protocols/category
  [category] (make-compositional-unital-quiver category))

(defmethod to-copresheaf :locus.elementary.copresheaf.core.protocols/groupoid
  [groupoid] (make-compositional-dependency-quiver groupoid))

; An nary-quiver is a generalisation of quivers for dealing with
; higher order nary-relations. In particular, there are ternary quivers
; which are the set valued functors which correspond most readily
; to ternary relations.
(defn nary-quiver-copresheaf
  ([rel]
   (nary-quiver-copresheaf
     (count (first rel))
     (vertices rel)
     rel))
  ([n vertices edges]
   (Copresheaf.
     (nary-quiver-category n)
     (fn [obj]
       (case obj
         "edges" edges
         "vertices" vertices))
     (fn [arrow]
       (cond
         (= arrow "1ₑ") (identity-function edges)
         (= arrow "1ᵥ") (identity-function vertices)
         :else (SetFunction.
                 edges
                 vertices
                 (fn [edge]
                   (nth edge arrow))))))))

(defn ternary-quiver-copresheaf
  ([edges]
   (nary-quiver-copresheaf 3 (vertices edges) edges))
  ([vertices edges]
   (nary-quiver-copresheaf 3 vertices edges)))

(defn quaternary-quiver-copresheaf
  ([edges]
   (nary-quiver-copresheaf 4 (vertices edges) edges))
  ([vertices edges]
   (nary-quiver-copresheaf 4 vertices edges)))

; Generalizations of morphisms of functions described as presheaves
(defn higher-diamond
  [& triangles]

  (let [n (count triangles)
        target-number (inc n)]
    (letfn [(nth-set [i]
              (cond
                (= i 0) (triangle-source (first triangles))
                (= i target-number) (triangle-target (first triangles))
                :else (triangle-middle
                        (nth triangles (dec i)))))
            (get-function [[i j]]
              (cond
                (= i j) (identity-function (nth-set i))
                (= i 0) (prefunction (nth triangles (dec j)))
                (= j target-number) (postfunction (nth triangles (dec i)))))]
      (Copresheaf.
        (nth-higher-diamond-category n)
        nth-set
        get-function))))

; The idea of a different composition diamond allows us to give a different
; take on the basic idea of a diamond copresheaf, which is so fundamental
; to our theory of the topos of functions
(defn different-composition-diamond-copresheaf
  [^SetTriangle first-triangle, ^SetTriangle second-triangle]

  (letfn [(nth-set [obj]
            (case obj
              0 (triangle-source first-triangle)
              1 (triangle-middle first-triangle)
              2 (triangle-middle second-triangle)
              3 (triangle-target first-triangle)))]
    (Copresheaf.
      different-composition-diamond
      nth-set
      (fn [arrow]
        (cond
          (= arrow '(0 0)) (identity-function (nth-set 0))
          (= arrow '(1 1)) (identity-function (nth-set 1))
          (= arrow '(2 2)) (identity-function (nth-set 2))
          (= arrow '(3 3)) (identity-function (nth-set 3))
          (= arrow '(0 1)) (prefunction first-triangle)
          (= arrow '(0 2)) (prefunction second-triangle)
          (= arrow '(1 3)) (postfunction first-triangle)
          (= arrow '(2 3)) (postfunction second-triangle)
          (= arrow '(0 1 3)) (compfunction first-triangle)
          (= arrow '(0 2 3)) (compfunction second-triangle))))))

; A means by which we can create an nset copresheaf
(defn nset-copresheaf
  [coll]

  (->Copresheaf
    (nth-discrete-category (count coll))
    (fn [i]
      (nth coll i))
    (fn [i]
      (identity-function (nth coll i)))))

; Create a constant copresheaf from a category and some set
(defn constant-copresheaf
  [category coll]

  (->Copresheaf
    category
    (constantly coll)
    (constantly (identity-function coll))))

; Copresheaves over free categories are good ways of describing concrete quivers
(defn free-copresheaf
  [quiver morphism-function object-function]

  (->Copresheaf
    (free-category quiver)
    (fn [obj]
      (object-function obj))
    (fn [[start end path]]
      (apply
        compose
        (map
          morphism-function
          path)))))

; Convert copresheaves to functors
(defmethod to-functor Copresheaf
  [^Copresheaf func]

  (Functor.
    (source-object func)
    (target-object func)
    (.morphism_function func)
    (.object_function func)))

; Every single object of a copresheaf is an MSet
(defn get-mset-by-object
  [copresheaf x]

  (let [cat (index copresheaf)]
    (->MSet
      (endomorphism-monoid cat x)
      (get-set copresheaf x)
      (fn [action x]
        ((get-function copresheaf action) x)))))

; Change of category functors for topoi of copresheaves
(defn change-of-category
  [functor copresheaf]

  (Copresheaf.
    (source-object functor)
    (fn [obj]
      (object-apply copresheaf (object-apply functor obj)))
    (fn [morphism]
      (morphism-apply copresheaf (morphism-apply functor morphism)))))

; Try to reduce the index category of a copresheaf
(defn subindex
  [copresheaf new-morphisms new-objects]

  (->Copresheaf
    (restrict-category (index copresheaf) new-morphisms new-objects)
    (partial get-set copresheaf)
    (partial get-function copresheaf)))

(defn wide-subindex
  [copresheaf new-morphisms]

  (->Copresheaf
    (wide-subcategory (index copresheaf) new-morphisms)
    (partial get-set copresheaf)
    (partial get-function copresheaf)))

(defn full-subindex
  [copresheaf new-objects]

  (->Copresheaf
    (full-subcategory (index copresheaf) new-objects)
    (partial get-set copresheaf)
    (partial get-function copresheaf)))

; Combining two copresheaves over their index categories
(defn index-sum
  [& copresheaves]

  (->Copresheaf
    (apply category-coproduct (map index copresheaves))
    (fn [[i obj]]
      (get-set (nth copresheaves i) obj))
    (fn [[i arrow]]
      (get-function (nth copresheaves i) arrow))))

; Products and coproducts of copresheaves
; The products and coproducts of copresheaves are defined componentwise.
; The same is true dually for presheaves. The products and coproducts
; are always defined for any topos of copresheaves.
(defmethod product Copresheaf
  [& copresheaves]

  (Copresheaf.
    (.category (first copresheaves))
    (fn [obj]
      (apply
        product
        (map
          (fn [copresheaf]
            (object-apply copresheaf obj))
          copresheaves)))
    (fn [morphism]
      (apply
        product
        (map
          (fn [copresheaf]
            (morphism-apply copresheaf morphism))
          copresheaves)))))

(defmethod coproduct Copresheaf
  [& copresheaves]

  (Copresheaf.
    (.category (first copresheaves))
    (fn [obj]
      (apply
        coproduct
        (map
          (fn [copresheaf]
            (object-apply copresheaf obj))
          copresheaves)))
    (fn [morphism]
      (apply
        coproduct
        (map
          (fn [copresheaf]
            (morphism-apply copresheaf morphism))
          copresheaves)))))

; The section preorder of a copresheaf
(defn sections
  [copresheaf]

  (set
    (mapcat
      (fn [obj]
        (map
          (fn [i]
            (list obj i))
          (get-set copresheaf obj)))
      (objects (index copresheaf)))))

(defn ^{:private true} section-relation-from-function
  [copresheaf arrow]

  (let [cat (index copresheaf)
        source (source-element cat arrow)
        target (target-element cat arrow)
        func (get-function copresheaf arrow)]
    (set
      (map
       (fn [[a b]]
         (list (list source a) (list target b)))
       (underlying-relation func)))))

(defn section-preorder
  [copresheaf]

  (apply
    union
    (map
      (fn [arrow]
        (section-relation-from-function copresheaf arrow))
      (morphisms (index copresheaf)))))

; Subalgebra lattices of copresheaves
(defn closed-inclusion-map?
  [copresheaf inclusion-map]

  (let [index-category (source-object copresheaf)
        arrows (morphisms index-category)]
    (every?
      (fn [arrow]
        (let [func (morphism-apply copresheaf arrow)
              source (source-element index-category arrow)
              target (target-element index-category arrow)
              image (set-image func (inclusion-map source))
              target-set (inclusion-map target)]
          (superset?
            (list image target-set))))
      arrows)))

(defn all-inclusion-maps
  [copresheaf]

  (let [index-category (source-object copresheaf)
        objs (seq (objects index-category))
        sets (map
               (partial object-apply copresheaf)
               objs)]
    (for [i (apply
              cartesian-product
              (map power-set sets))]
      (zipmap objs i))))

(defn closed-inclusion-maps
  [copresheaf]

  (filter
    (partial closed-inclusion-map? copresheaf)
    (all-inclusion-maps copresheaf)))

(defmethod sub Copresheaf
  [copresheaf]

  (letfn [(componentwise-apply [func a b]
            (let [k (keys a)]
              (zipmap
                k
                (map
                  (fn [i]
                    (func (a i) (b i)))
                  k))))]
    (Lattice.
      (set (closed-inclusion-maps copresheaf))
      (monoidalize
        (fn [a b]
          (componentwise-apply union a b)))
      (monoidalize
        (fn [a b]
          (componentwise-apply intersection a b))))))

; Generalized mechanism for determining the appropriate data type for storing
; given copresheaf. Using this method, we can have an overall organization of our
; entire topos theoretic system.
(defn structure-description
  [func]

  (let [index-category (index func)
        objects-count (count (objects index-category))
        morphisms-count (count (morphisms index-category))
        proper-morphisms-count (- morphisms-count objects-count)]
    (if (thin-category? index-category)
      (if (thin-groupoid? index-category)
        (cond
          (and (= objects-count 1) (= morphisms-count 1)) "SET"
          (and (= objects-count 2) (= morphisms-count 2)) "DISET"
          (and (= objects-count 2) (= morphisms-count 4)) "BIJECTION"
          (and (= objects-count 3) (= morphisms-count 3)) "TRISET"
          (and (= objects-count 3) (complete-thin-groupoid? index-category)) "TRIJECTION"
          (and (= objects-count 4) (two-regular-thin-groupoid? index-category)) "DIBIJECTION"
          (discrete-category? index-category) "NSET"
          (complete-thin-groupoid? index-category) "MULTIJECTION"
          (two-regular-thin-groupoid? index-category) "NBIJECTION"
          :else "NMULTIJECTION")
        (cond
          (and (= objects-count 2) (= morphisms-count 3)) "FUNCTION"
          (and (= objects-count 3) (n-cospan-category? index-category)) "COSPAN"
          (and (= objects-count 3) (n-span-category? index-category)) "SPAN"
          (n-span-category? index-category) "NSPAN"
          (n-cospan-category? index-category) "NCOSPAN"
          (and (= objects-count 3) (total-order-category? index-category)) "TRIANGLE"
          (total-order-category? index-category) "CHAIN COPRESHEAF"
          (and (= objects-count 4) (n-pair-category? index-category)) "DIFUNCTION"
          (diamond-category? index-category) "DIAMOND"
          (and (= objects-count 8) (n-diamond-category? index-category)) "DIDIAMOND"
          (and (= objects-count 8) (n-gem-category? index-category)) "DIGEM"
          (n-diamond-category? index-category) "NDIAMOND"
          (higher-diamond-category? index-category) "HIGHER DIAMOND"
          (n-gem-category? index-category) "NGEM"
          (gem-category? index-category) "GEM"
          (n-pair-category? index-category) "NFUNCTION"
          :else "DEPENDENCY"))
      (case objects-count
        1 "MSET"
        2 (if (n-arrow-category? index-category)
            (case proper-morphisms-count
              2 "QUIVER"
              3 "TERNARY QUIVER"
              4 "QUATERNARY QUIVER"
              "NQUIVER")
            (if (permutable-quiver-index-category? index-category)
              "PERMUTABLE QUIVER"
              "COPRESHEAF"))
        "COPRESHEAF"))))

; Ontology of copresheaves
(defn copresheaf?
  [obj]

  (= (type obj) Copresheaf))