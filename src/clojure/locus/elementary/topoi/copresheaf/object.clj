(ns locus.elementary.topoi.copresheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.base.effects.global.identity :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.difunction.dibijection.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.bijection.core.morphism :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.quiver.permutable.morphism :refer :all]
            [locus.elementary.quiver.dependency.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.dependency.chain.object :refer :all]
            [locus.elementary.dependency.nset.object :refer :all]
            [locus.elementary.dependency.nfunction.object :refer :all]
            [locus.elementary.dependency.nfunction.nbijection :refer :all]
            [locus.elementary.category.core.generated-category :refer :all]
            [locus.elementary.cospan.core.object :refer :all]
            [locus.elementary.triangle.core.object :refer :all]
            [locus.elementary.dependency.core.object :refer :all]
            [locus.elementary.triangle.core.morphism :refer :all]
            [locus.elementary.incidence.core.morphism :refer :all]
            [locus.elementary.cospan.core.morphism :refer :all]
            [locus.elementary.diamond.core.morphism :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all])
  (:import (locus.elementary.category.core.morphism Functor)
           (locus.elementary.lattice.core.object Lattice)
           (locus.elementary.action.global.object MSet)
           (locus.base.function.core.object SetFunction)
           (locus.elementary.quiver.core.object Quiver)
           (locus.elementary.dependency.nset.object NSet)
           (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.quiver.permutable.object PermutableQuiver)
           (locus.elementary.quiver.unital.object UnitalQuiver)
           (locus.elementary.quiver.dependency.object DependencyQuiver)
           (locus.elementary.dependency.nfunction.object NFunction)
           (locus.elementary.difunction.core.object Difunction)
           (locus.elementary.bijection.core.morphism Gem)
           (locus.elementary.incidence.core.object Span)
           (locus.elementary.cospan.core.object Cospan)
           (locus.elementary.triangle.core.object TriangleCopresheaf)
           (locus.elementary.dependency.nfunction.nbijection NBijection)
           (locus.elementary.difunction.dibijection.object Dibijection)
           (locus.elementary.dependency.chain.object ChainCopresheaf)
           (locus.elementary.dependency.core.object Dependency)
           (locus.elementary.two_quiver.core.object TwoQuiver)
           (locus.elementary.triangle.core.morphism TriangleMorphism)
           (locus.elementary.incidence.core.morphism MorphismOfSpans)
           (locus.elementary.cospan.core.morphism MorphismOfCospans)
           (locus.elementary.diamond.core.morphism Cube)
           (locus.elementary.ternary_quiver.core.object TernaryQuiver)
           (locus.elementary.quiver.core.morphism MorphismOfQuivers)
           (locus.elementary.quiver.unital.morphism MorphismOfUnitalQuivers)
           (locus.elementary.quiver.permutable.morphism MorphismOfPermutableQuivers)
           (locus.elementary.quiver.dependency.morphism MorphismOfDependencyQuivers)))

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

; Index categories for the fundamental topoi of sets and functions
(def trivial-category
  (simple-labeled-category
    #{"Set"}
    {"Identity" ["Set" "Set"]}))

(def t2-category
  (adjoin-generators
    (simple-labeled-category
      #{"Input" "Output"}
      {"1ᵢ" ["Input" "Input"]
       "1ₒ" ["Output" "Output"]
       "f"  ["Input" "Output"]})
    #{"f"}))

; Index categories for disets and bijections
(def e2-category
  (nth-discrete-category 2))

(def k2-category
  (adjoin-generators
    (simple-labeled-category
      #{"Input" "Output"}
      {"1ᵢ"  ["Input" "Input"]
       "1ₒ"  ["Output" "Output"]
       "f"   ["Input" "Output"]
       "f⁻¹" ["Output" "Input"]})
    #{"f" "f⁻¹"}))

; Spans, cospans, and triangles
(def incidence-category*
  (adjoin-generators
    (simple-labeled-category
      #{"flags" "lines" "points"}
      {"1_flags"  ["flags" "flags"]
       "1_lines"  ["lines" "lines"]
       "1_points" ["points" "points"]
       "point"    ["flags" "points"]
       "line"     ["flags" "lines"]})
    #{"point" "line"}))

(def two-cospan-category
  (adjoin-generators
    (simple-labeled-category
      #{"a" "b" "c"}
      {"1a" ["a" "a"]
       "1b" ["b" "b"]
       "1c" ["c" "c"]
       "f"  ["a" "c"]
       "g"  ["b" "c"]})
    #{"f" "g"}))

(def triangle-category
  (adjoin-generators
    (simple-labeled-category
      #{"a" "b" "c"}
      {"1a"    ["a" "a"]
       "1b"    ["b" "b"]
       "1c"    ["c" "c"]
       "f"     ["a" "b"]
       "g"     ["b" "c"]
       "g ⚬ f" ["a" "c"]})
    '#{"f" "g"}))

; Diamond and gem categories
(def diamond-category
  (adjoin-generators
    (simple-labeled-category
      #{"a" "b" "c" "d"}
      {"1a" ["a" "a"]
       "1b" ["b" "b"]
       "1c" ["c" "c"]
       "1d" ["d" "d"]
       "f"  ["a" "b"]
       "g"  ["c" "d"]
       "i"  ["a" "c"]
       "o"  ["b" "d"]
       "c"  ["a" "d"]})
    '#{"f" "g" "i" "o"}))

(def gem-category
  (adjoin-generators
    (thin-category
      (set (map seq (total-preorder [#{0 1} #{2 3}]))))
    '#{(0 1) (1 0) (2 3) (3 2) (0 2) (1 3)}))

; Non-thin categories
; In particular, these are index categories for the various types of quivers that have emerged
; as an important part of our ontology of copresheaves. We see that aside from the dependecny functors
; and MSets, quivers tend to be among the most common objects of presheaf theory. They are widely
; used and a number of other structures can be constructed from them.
(def t2*
  (adjoin-generators
    (simple-labeled-category
      #{"edges" "vertices"}
      {"1ₑ"     ["edges" "edges"]
       "1ᵥ"     ["vertices" "vertices"]
       "source" ["edges" "vertices"]
       "target" ["edges" "vertices"]})
    '#{"source" "target"}))

; Different composition
(def different-composition-diamond
  (adjoin-composition
    (create-unital-quiver
      {"0" '(0 0)
       "1" '(1 1)
       "2" '(2 2)
       "3" '(3 3)}
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

; Index categories for special types of generalized quivers: there are several examples of
; these index categories for the different types of cases: permutable quivers, dependency
; quivers, unital quivers, etc. Each of them has their own role to play in describing
; the topos theory of some kind of mathematical structure.

; The index category of the topos of undirected graphs and permutable quivers
(def permutable-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"  ["edges" "vertices"]
         "target"  ["edges" "vertices"]
         "reverse" ["edges" "edges"]})
      (fn [[a b]]
        (cond
          (or (= a "1ₑ") (= a "1ᵥ")) b
          (or (= b "1ₑ") (= b "1ᵥ")) a

          (and (= a "source") (= b "reverse")) "target"
          (and (= a "target") (= b "reverse")) "source"

          (and (= a "reverse") (= b "reverse")) "1ₑ")))
    '#{"source" "target" "reverse"}))

; Unital quivers theory
(def unital-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"   ["edges" "vertices"]
         "target"   ["edges" "vertices"]
         "identity" ["vertices" "edges"]
         "idt"      ["edges" "edges"]
         "ids"      ["edges" "edges"]})
      (fn [[a b]]
        (letfn [(component-function? [x]
                  (or (= x "source") (= x "target")))
                (component-identity? [x]
                  (or (= x "idt") (= x "ids")))]
          (cond
            ; identities
            (or (= a "1ₑ") (= a "1ᵥ")) b
            (or (= b "1ₑ") (= b "1ᵥ")) a

            ; the edge monoid action
            (and (component-identity? a) (component-identity? b)) b

            ; preceding edge actions
            (and (component-function? a) (= b "ids")) "source"
            (and (component-function? a) (= b "idt")) "target"

            ; successor edge actions
            (and (component-identity? a) (= b "identity")) "identity"

            ; vertex first composition of identities and component functions
            (and (component-function? a) (= b "identity")) "1ᵥ"

            ; source and target identities
            (and (= a "identity") (= b "source")) "ids"
            (and (= a "identity") (= b "target")) "idt"))))
    '#{"source" "target" "identity"}))

; Dependency quivers theory
(def dependency-quiver-index-category
  (adjoin-generators
    (adjoin-composition
      (create-unital-quiver
        {"edges"    "1ₑ"
         "vertices" "1ᵥ"}
        {"source"   ["edges" "vertices"]
         "target"   ["edges" "vertices"]
         "identity" ["vertices" "edges"]
         "idt"      ["edges" "edges"]
         "ids"      ["edges" "edges"]
         "reverse"  ["edges" "edges"]})
      (fn [[a b]]
        (letfn [(component-function? [x]
                  (or (= x "source") (= x "target")))
                (component-identity? [x]
                  (or (= x "idt") (= x "ids")))]
          (cond
            ; identities
            (or (= a "1ₑ") (= a "1ᵥ")) b
            (or (= b "1ₑ") (= b "1ᵥ")) a

            ; the edge monoid action
            (and (component-identity? a) (component-identity? b)) b

            ; preceding edge actions
            (and (component-function? a) (= b "ids")) "source"
            (and (component-function? a) (= b "idt")) "target"

            ; successor edge actions
            (and (component-identity? a) (= b "identity")) "identity"

            ; vertex first composition of identities and component functions
            (and (component-function? a) (= b "identity")) "1ᵥ"

            ; source and target identities
            (and (= a "identity") (= b "source")) "ids"
            (and (= a "identity") (= b "target")) "idt"

            ; permutable quiver theory
            (and (= a "source") (= b "reverse")) "target"
            (and (= a "target") (= b "reverse")) "source"
            (and (= a "reverse") (= b "reverse")) "1ₑ"

            ; effects on identities
            (and (= a "reverse") (= b "identity")) "identity"
            (and (= a "reverse") (= b "ids")) "ids"
            (and (= a "reverse") (= b "idt")) "idt"
            (and (= a "ids") (= b "reverse")) "idt"
            (and (= a "idt") (= b "reverse")) "ids"))))
    '#{"source" "target" "identity" "reverse"}))

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

(def t3*
  (nary-quiver-category 3))

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

; We see that many forms of quivers have been introduced in to our ontology as part of our basic
; understanding of topos theoretic presheaf theory. However, in our investigations it often
; becomes necessary to consider various forms of two quivers. That is what we are dealing with
; now. These two quiver copresheaves, such as two globular sets, are our basic presheaf theoretic
; model for higher category theory.

; Two quiver index categories
(def two-quiver-index-category
  (adjoin-composition
    (create-unital-quiver
      {"c2" "ic2"
       "c1" "ic1"
       "c0" "ic0"}
      {"1s"  ["c1" "c0"]
       "1t"  ["c1" "c0"]
       "2s"  ["c2" "c1"]
       "2t"  ["c2" "c1"]
       "2ss" ["c2" "c0"]
       "2st" ["c2" "c0"]
       "2ts" ["c2" "c0"]
       "2tt" ["c2" "c0"]})
    (fn [[a b]]
      (letfn [(identity-arrow? [x]
                (contains? #{"ic0" "ic1" "ic2"} x))]
        (cond
          (identity-arrow? a) b
          (identity-arrow? b) a
          (and (= a "1s") (= b "2s")) "2ss"
          (and (= a "1t") (= b "2s")) "2st"
          (and (= a "1s") (= b "2t")) "2ts"
          (and (= a "1t") (= b "2t")) "2tt")))))

; Path quiver index category
(def path-quiver-index-category
  (adjoin-composition
    (create-unital-quiver
      {"c2" "ic2"
       "c1" "ic1"
       "c0" "ic0"}
      {"1s" ["c1" "c0"]
       "1t" ["c1" "c0"]
       "2s" ["c2" "c1"]
       "2t" ["c2" "c1"]
       "2m" ["c2" "c0"]
       "2l" ["c2" "c0"]
       "2f" ["c2" "c0"]})
    (fn [[a b]]
      (letfn [(identity-arrow? [x]
                (contains? #{"ic0" "ic1" "ic2"} x))]
        (cond
          (identity-arrow? a) b
          (identity-arrow? b) a
          (and (= a "1s") (= b "2s")) "2m"
          (and (= a "1t") (= b "2s")) "2l"
          (and (= a "1s") (= b "2t")) "2f"
          (and (= a "1t") (= b "2t")) "2m")))))

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

; A general mechanism for getting the index categories of copresheaves
; The index category is the source object of the copresheaf, which is always dependent upon the
; data type of the copresheaf in question. The index category determines the topos that the
; copresheaf belongs to and its properties.
(defmulti index-category type)

(defmethod index-category :locus.base.logic.core.set/universal
  [coll] trivial-category)

(defmethod index-category :locus.base.logic.structure.protocols/set-function
  [coll] t2-category)

(defmethod index-category :locus.elementary.copresheaf.core.protocols/diset
  [coll] e2-category)

(defmethod index-category :locus.elementary.copresheaf.core.protocols/bijection
  [bijection] k2-category)

(defmethod index-category Span
  [span] incidence-category*)

(defmethod index-category Cospan
  [cospan] two-cospan-category)

(defmethod index-category TriangleCopresheaf
  [triangle] triangle-category)

(defmethod index-category Quiver
  [quiver] t2*)

(defmethod index-category UnitalQuiver
  [unital-quiver] unital-quiver-index-category)

(defmethod index-category PermutableQuiver
  [permutable-quiver] permutable-quiver-index-category)

(defmethod index-category DependencyQuiver
  [dependency-quiver] dependency-quiver-index-category)

(defmethod index-category Diamond
  [diamond] diamond-category)

(defmethod index-category Gem
  [gem] gem-category)

(defmethod index-category MSet
  [^MSet mset] (.-monoid mset))

(defmethod index-category Dependency
  [^Dependency dependency] (.-order dependency))

(defmethod index-category NSet
  [^NSet nset] (nth-discrete-category (nset-type nset)))

(defmethod index-category NFunction
  [^NFunction nfunction] (n-pair-category (count (.-funcs nfunction))))

(defmethod index-category NBijection
  [^NBijection nbijection] (unordered-n-pair-category (count (.-bijections nbijection))))

(defmethod index-category Difunction
  [^Difunction difunction] (n-pair-category 2))

(defmethod index-category Dibijection
  [^Dibijection dibijection] (unordered-n-pair-category 2))

(defmethod index-category ChainCopresheaf
  [^ChainCopresheaf chain] (nth-total-order-category (chain-type chain)))

(defmethod index-category Copresheaf
  [^Copresheaf copresheaf] (.-category copresheaf))

(defmethod index-category TernaryQuiver
  [ternary-quiver] (n-quiver-index-category 3))

(defmethod index-category TwoQuiver
  [two-quiver] two-quiver-index-category)

(defmethod index-category :locus.elementary.copresheaf.core.protocols/partial-magmoid
  [obj] compositional-quiver-index-category)

(defmethod index-category :locus.elementary.copresheaf.core.protocols/unital-magmoid
  [obj] compositional-unital-quiver-index-category)

(defmethod index-category :locus.elementary.copresheaf.core.protocols/groupoid
  [groupoid] compositional-dependency-quiver-index-category)

; Every morphism in a topos of copresheaves corresponds to a copresheaf
(defn create-copresheaf-by-morphism
  [source target func]

  (let [index-category (index-category source)
        double-index-category (double-category index-category)]
    (Copresheaf.
      double-index-category
      (fn [[i v]]
        (case i
          0 (object-apply source v)
          1 (object-apply target v)))
      (fn [[i v]]
        (case i
          0 (morphism-apply source v)
          1 (morphism-apply target v)
          2 (compose
              (morphism-apply target v)
              (func (source-element index-category v))))))))

; General conversion routines for the most basic topos objects
; The various fundamental constructs of our ontology, which is rooted in
; topos theory can all be converted to copresheaves. This leads to an
; extensive system of conversion methods.
(defmulti to-copresheaf type)

(defmethod to-copresheaf Copresheaf
  [func] func)

(defmethod to-copresheaf :locus.base.logic.core.set/universal
  [coll]

  (Copresheaf.
    trivial-category
    (fn [obj] coll)
    (fn [morphism] (identity-function coll))))

(defmethod to-copresheaf :locus.base.logic.structure.protocols/set-function
  [func]

  (Copresheaf.
    t2-category
    (fn [obj]
      (case obj
        "Input" (first-set func)
        "Output" (second-set func)))
    (fn [morphism]
      (cond
        (= morphism "1ᵢ") (identity-function (first-set func))
        (= morphism "1ₒ") (identity-function (second-set func))
        (= morphism "f") func))))

; Convert copresheaves over preorders into more general copresheaves
; Let P be a preorder, then Sets^P is a topos consisting of all copresheaves over the preorder
; P. This is a fruitful means of exploring the properties of the preorder P. The resulting
; copresheaves generalize functional dependencies of relations, so they are often called
; dependency functors as a result. We can convert these dependency functors into more
; general copresheaves using the following method.
(defmethod to-copresheaf Dependency
  [^Dependency dependency]

  (->Copresheaf
    (.-order dependency)
    (.-object_function dependency)
    (.-morphism_function dependency)))

; Conversion routines for special classes of copresheaves with arbitrary size index categories
; These conversion routines will simply fall back on the dependency functors in order to reuse
; their implementation of the conversion routine.
(defmethod to-copresheaf Diset
  [diset] (to-copresheaf (to-dependency diset)))

(defmethod to-copresheaf Bijection
  [bijection] (to-copresheaf (to-dependency bijection)))

(defmethod to-copresheaf NSet
  [nset] (to-copresheaf (to-dependency nset)))

(defmethod to-copresheaf NFunction
  [nfunction] (to-copresheaf (to-dependency nfunction)))

(defmethod to-copresheaf Difunction
  [difunction] (to-copresheaf (to-dependency difunction)))

(defmethod to-copresheaf NBijection
  [nbijection] (to-copresheaf (to-dependency nbijection)))

(defmethod to-copresheaf Dibijection
  [dibijection] (to-copresheaf (to-dependency dibijection)))

(defmethod to-copresheaf ChainCopresheaf
  [chain] (to-copresheaf (to-dependency chain)))

(defmethod to-copresheaf TriangleMorphism
  [morphism] (to-copresheaf (to-dependency morphism)))

(defmethod to-copresheaf MorphismOfSpans
  [morphism] (to-copresheaf (to-dependency morphism)))

(defmethod to-copresheaf MorphismOfCospans
  [morphism] (to-copresheaf (to-dependency morphism)))

(defmethod to-copresheaf MorphismOfSpans
  [morphism] (to-copresheaf (to-dependency morphism)))

(defmethod to-copresheaf Cube
  [cube] (to-copresheaf (to-dependency cube)))

(defmethod to-copresheaf Diamond
  [diamond] (to-copresheaf (to-dependency diamond)))

(defmethod to-copresheaf Gem
  [gem] (to-copresheaf (to-dependency gem)))

(defmethod to-copresheaf TriangleCopresheaf
  [triangle] (to-copresheaf (to-dependency triangle)))

(defmethod to-copresheaf Span
  [span] (to-copresheaf (to-dependency span)))

(defmethod to-copresheaf Cospan
  [cospan] (to-copresheaf (to-dependency cospan)))

; Copresheaves over monoids
(defmethod to-copresheaf :locus.elementary.copresheaf.core.protocols/mset
  [^MSet ms]

  (Copresheaf.
    (.monoid ms)
    (fn [obj]
      (underlying-set ms))
    (fn [elem]
      (action-function ms elem))))

; Additional classes of copresheaves
(defmethod to-copresheaf Quiver
  [quiv]

  (Copresheaf.
    t2*
    (fn [obj]
      (case obj
        "edges" (first-set quiv)
        "vertices" (second-set quiv)))
    (fn [morphism]
      (case morphism
        "1ₑ" (identity-function (first-set quiv))
        "1ᵥ" (identity-function (second-set quiv))
        "source" (source-function quiv)
        "target" (target-function quiv)))))

(defmethod to-copresheaf PermutableQuiver
  [quiv]

  (Copresheaf.
    permutable-quiver-index-category
    (fn [obj]
      (case obj
        "edges" (first-set quiv)
        "vertices" (second-set quiv)))
    (fn [arrow]
      (case arrow
        "1ₑ" (identity-function (first-set quiv))
        "1ᵥ" (identity-function (second-set quiv))
        "source" (source-function quiv)
        "target" (target-function quiv)
        "reverse" (inverse-function quiv)))))

(defmethod to-copresheaf UnitalQuiver
  [quiv]

  (Copresheaf.
    unital-quiver-index-category
    (fn [obj]
      (case obj
        "edges" (first-set quiv)
        "vertices" (second-set quiv)))
    (fn [arrow]
      (case arrow
        "1ₑ" (identity-function (first-set quiv))
        "1ᵥ" (identity-function (second-set quiv))
        "source" (source-function quiv)
        "target" (target-function quiv)
        "identity" (identity-element-function quiv)
        "ids" (source-identity-function quiv)
        "idt" (target-identity-function quiv)))))

(defmethod to-copresheaf DependencyQuiver
  [quiv]

  (Copresheaf.
    dependency-quiver-index-category
    (fn [obj]
      (case obj
        "edges" (first-set quiv)
        "vertices" (second-set quiv)))
    (fn [arrow]
      (case arrow
        "1ₑ" (identity-function (first-set quiv))
        "1ᵥ" (identity-function (second-set quiv))
        "source" (source-function quiv)
        "target" (target-function quiv)
        "identity" (identity-element-function quiv)
        "ids" (source-identity-function quiv)
        "idt" (target-identity-function quiv)
        "reverse" (inverse-function quiv)))))

; Conversion of morphisms of quivers into copresheaves
(defn create-copresheaf-by-morphism-of-quivers
  [morphism]

  (->Copresheaf
    (to-copresheaf (source-object morphism))
    (to-copresheaf (target-object morphism))
    (fn [obj]
      (case obj
        "edges" (morphism-component-function morphism)
        "vertices" (object-component-function morphism)))))

(defmethod to-copresheaf MorphismOfQuivers
  [morphism] (create-copresheaf-by-morphism-of-quivers morphism))

(defmethod to-copresheaf MorphismOfUnitalQuivers
  [morphism] (create-copresheaf-by-morphism-of-quivers morphism))

(defmethod to-copresheaf MorphismOfPermutableQuivers
  [morphism] (create-copresheaf-by-morphism-of-quivers morphism))

(defmethod to-copresheaf MorphismOfDependencyQuivers
  [morphism] (create-copresheaf-by-morphism-of-quivers morphism))

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

; Convert two quivers into two copresheafs using topos theory
(defmethod to-copresheaf TwoQuiver
  [two-quiver]

  (->Copresheaf
    two-quiver-index-category
    (fn [obj]
      (case obj
        "c0" (objects two-quiver)
        "c1" (morphisms two-quiver)
        "c2" (two-morphisms two-quiver)))
    (fn [arrow]
      (case arrow
        "ic0" (identity-function (objects two-quiver))
        "ic1" (identity-function (morphisms two-quiver))
        "ic2" (identity-function (two-morphisms two-quiver))
        "1s" (source-function two-quiver)
        "1t" (target-function two-quiver)
        "2s" (s-function two-quiver)
        "2t" (t-function two-quiver)
        "2ss" (ss-function two-quiver)
        "2st" (st-function two-quiver)
        "2ts" (ts-function two-quiver)
        "2tt" (tt-function two-quiver)))))

; An nary-quiver is a generalisation of quivers for dealing with
; higher order nary-relations. In particular, there are ternary quivers
; which are the set valued functors which correspond most readily
; to ternary relations.
(defn nary-quiver
  ([rel]
   (nary-quiver
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

(defn ternary-quiver
  ([edges]
   (nary-quiver 3 (vertices edges) edges))
  ([vertices edges]
   (nary-quiver 3 vertices edges)))

(defn quaternary-quiver
  ([edges]
   (nary-quiver 4 (vertices edges) edges))
  ([vertices edges]
   (nary-quiver 4 vertices edges)))

; Convert ternary quivers into copresheaves
(defmethod to-copresheaf :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [ternary-quiver]

  (->Copresheaf
    (nary-quiver-category 3)
    (fn [obj]
      (case obj
        "edges" (morphisms ternary-quiver)
        "vertices" (objects ternary-quiver)))
    (fn [arrow]
      (cond
        (= arrow "1ₑ") (identity-function (morphisms ternary-quiver))
        (= arrow "1ᵥ") (identity-function (objects ternary-quiver))
        :else (case arrow
                0 (first-component-function ternary-quiver)
                1 (second-component-function ternary-quiver)
                2 (third-component-function ternary-quiver))))))

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
  [^TriangleCopresheaf first-triangle, ^TriangleCopresheaf second-triangle]

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

; Convert copresheaves to functors
(defmethod to-functor Copresheaf
  [^Copresheaf func]

  (Functor.
    (source-object func)
    (target-object func)
    (.morphism_function func)
    (.object_function func)))

; Change of category functors for topoi of copresheaves
(defn change-of-category
  [functor copresheaf]

  (Copresheaf.
    (source-object functor)
    (fn [obj]
      (object-apply copresheaf (object-apply functor obj)))
    (fn [morphism]
      (morphism-apply copresheaf (morphism-apply functor morphism)))))

; In the logic module we provided support for set systems and in the
; functional module we provided support for function systems, and now both
; of these two components are realised as part of the theory of copresheaves.
(defn copresheaf-sets
  [copresheaf]

  (let [index-category (source-object copresheaf)
        objects (second-set index-category)]
    (set
      (map
        (fn [obj]
          (object-apply copresheaf obj))
        objects))))

(defn copresheaf-functions
  [copresheaf]

  (let [index-category (source-object copresheaf)
        morphisms (first-set index-category)]
    (set
      (map
        (fn [morphism]
          (morphism-apply copresheaf morphism))
        morphisms))))

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

  (let [index-category (source-object func)
        objects-count (count (objects index-category))
        morphisms-count (count (morphisms index-category))
        proper-morphisms-count (- morphisms-count objects-count)]
    (if (and (= objects-count 1) (= morphisms-count 1))
      "SET"
      (if (thin-category? index-category)
        (if (thin-groupoid? index-category)
          (cond
            (and (= objects-count 2) (= morphisms-count 2)) "DISET"
            (and (= objects-count 2) (= morphisms-count 4)) "BIJECTION"
            (and (= objects-count 3) (= morphisms-count 3)) "TRISET"
            (and (= objects-count 3) (complete-thin-groupoid? index-category)) "TRIJECTION"
            (and (= objects-count 4) (two-regular-thin-groupoid? index-category)) "DIBIJECTION"
            (discrete-category? index-category) "NSET"
            (two-regular-thin-groupoid? index-category) "NBIJECTION"
            :else "COPRESHEAF")
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
            :else "COPRESHEAF"))
        (case objects-count
          1 "MSET"
          2 (if (n-arrow-category? index-category)
              (if (= proper-morphisms-count 2)
                "QUIVER"
                "NQUIVER")
              (if (permutable-quiver-index-category? index-category)
                "PERMUTABLE QUIVER"
                "COPRESHEAF"))
          "COPRESHEAF")))))

; Ontology of copresheaves
(defn copresheaf?
  [obj]

  (= (type obj) Copresheaf))
