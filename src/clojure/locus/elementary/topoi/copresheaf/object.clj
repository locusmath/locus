(ns locus.elementary.topoi.copresheaf.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.elementary.function.inclusion.identity :refer :all]
            [locus.elementary.incidence.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.gem.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.topoi.system.setrel :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.topoi.nset.object :refer :all]
            [locus.elementary.topoi.nset.morphism :refer :all]
            [locus.elementary.category.core.generated-category :refer :all])
  (:import (locus.elementary.action.global.object MSet)
           (locus.elementary.diset.core.object Diset)
           (locus.elementary.function.core.object SetFunction)
           (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.quiver.core.object Quiver)
           (locus.elementary.category.core.morphism Functor)
           (locus.elementary.lattice.core.object Lattice)
           (locus.elementary.topoi.nset.object NSet)
           (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.quiver.permutable.object PermutableQuiver)
           (locus.elementary.quiver.unital.object UnitalQuiver)
           (locus.elementary.quiver.dependency.object DependencyQuiver)
           (locus.elementary.topoi.nset.morphism NFunction)
           (locus.elementary.difunction.core.object Difunction)
           (locus.elementary.gem.core.object Gem)
           (locus.elementary.incidence.core.object Span)))

; Copresheaves
; A copresheaf is a set-valued functor and therefore an object of a topos Sets^(C). These are the primary
; objects of study in Locus. Using presheaf theoretic foundations, we model sets as presheaves over a
; single object and functions as presheaves over an ordered pair, and study different models of
; related structures defined by presheaves using the methods of topos theory.
(deftype Copresheaf [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] sets)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(defmethod to-functor Copresheaf
  [^Copresheaf func]

  (Functor.
    (source-object func)
    (target-object func)
    (.morphism_function func)
    (.object_function func)))

; This is an index category for morphisms of bijections
(def two-two-category
  (adjoin-generators
    (thin-category
     (set
       (map
         seq
         (total-preorder
           [#{0 1} #{2 3}]))))
    '#{(0 1) (1 0) (2 3) (3 2) (0 2) (1 3)}))

; Basic thin categories
(def trivial-category
  (simple-labeled-category
    #{"Set"}
    {"Identity" ["Set" "Set"]}))

(def e2-category
  (nth-discrete-category 2))

(def t2-category
  (adjoin-generators
    (simple-labeled-category
     #{"Input" "Output"}
     {"1ᵢ" ["Input" "Input"]
      "1ₒ" ["Output" "Output"]
      "f"  ["Input" "Output"]})
    #{"f"}))

(def k2-category
  (adjoin-generators
    (simple-labeled-category
     #{"Input" "Output"}
     {"1ᵢ"  ["Input" "Input"]
      "1ₒ"  ["Output" "Output"]
      "f"   ["Input" "Output"]
      "f⁻¹" ["Output" "Input"]})
    #{"f" "f⁻¹"}))

; Incidence categories and their duals
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

; Triangle categories are presheaves over the ordered triple category
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

; The diamond category of morphisms of functions
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

; Non-thin categories
(def t2*
  (adjoin-generators
    (simple-labeled-category
     #{"edges" "vertices"}
     {"1ₑ"     ["edges" "edges"]
      "1ᵥ"     ["vertices" "vertices"]
      "source" ["vertices" "edges"]
      "target" ["vertices" "edges"]})
    '#{"source" "target"}))

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

; Create a quiver
(def compositional-quiver-index-category
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

; This is a step towards defining compositional quivers
(def compositional-unital-quiver-index-category
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
               (compositional-quiver-arrow? [x]
                 (contains? #{"1ₑ" "1ᵥ" "source" "target" "∘" "∘ source" "∘ target"} x))]
         (cond
           (identity-arrow? a) b
           (identity-arrow? b) a
           (and
             (unital-quiver-arrow? a)
             (unital-quiver-arrow? b)) (unital-quiver-index-category (list a b))
           (and
             (compositional-quiver-arrow? a)
             (compositional-quiver-arrow? b)) (compositional-quiver-index-category (list a b))
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

; Compositional dependency quivers
(def compositional-dependency-quiver-index-category
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
         "∘ ids"    ["paths" "edges"]

         "reverse" ["edges" "edges"]
         "∘ reverse" ["paths" "edges"]})
      (fn [[a b]]
        (letfn [(identity-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ"} x))
                (dependency-quiver-arrow? [x]
                  (contains? #{"1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids" "reverse"} x))
                (compositional-unital-quiver-arrow? [x]
                  (contains? #{"1ₚ" "1ₑ" "1ᵥ" "source" "target" "identity" "idt" "ids"
                               "∘" "∘ source" "∘ target" "∘ ids" "∘ idt"} x))]
          (cond
            (identity-arrow? a) b
            (identity-arrow? b) a
            (and
              (dependency-quiver-arrow? a)
              (dependency-quiver-arrow? b)) (dependency-quiver-index-category (list a b))
            (and
              (compositional-unital-quiver-arrow? a)
              (compositional-unital-quiver-arrow? b)) (compositional-unital-quiver-index-category (list a b))

            (and (= a "reverse") (= b "∘")) "∘ reverse"
            (and (= a "reverse") (= b "∘ ids")) "∘ ids"
            (and (= a "reverse") (= b "∘ idt")) "∘ idt"

            (and (= a "reverse") (= b "∘ reverse")) "∘"
            (and (= a "source")  (= b "∘ reverse")) "∘ target"
            (and (= a "target")  (= b "∘ reverse")) "∘ source"
            (and (= a "ids") (= b "∘ reverse")) "∘ idt"
            (and (= a "idt") (= b "∘ reverse")) "∘ ids"))))
    '#{"source" "target" "∘" "identity" "reverse"}))

; General conversion routines for the most basic topos objects
; The various fundamental constructs of our ontology, which is rooted in
; topos theory can all be converted to copresheaves. This leads to an
; extensive system of conversion methods.
(defmulti to-copresheaf type)

(defmethod to-copresheaf Copresheaf
  [func] func)

(defmethod to-copresheaf :default
  [coll]

  (if (universal? coll)
   (Copresheaf.
     trivial-category
     (fn [obj] coll)
     (fn [morphism] (identity-function coll)))))

(defmethod to-copresheaf Diset
  [pair]

  (Copresheaf.
    e2-category
    (fn [obj]
      (case obj
        0 (first-set pair)
        1 (second-set pair)))
    (fn [morphism]
      (cond
        (= morphism 0) (identity-function (first-set pair))
        (= morphism 1) (identity-function (second-set pair))))))

(defmethod to-copresheaf :locus.elementary.function.core.protocols/set-function
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

(defmethod to-copresheaf Bijection
  [func]

  (Copresheaf.
    k2-category
    (fn [obj]
      (case obj
        "Input" (first-set func)
        "Output" (second-set func)))
    (fn [morphism]
      (cond
        (= morphism "1ᵢ") (identity-function (first-set func))
        (= morphism "1ₒ") (identity-function (second-set func))
        (= morphism "f") (underlying-function func)
        (= morphism "f⁻¹") (underlying-function (inv func))))))

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

(defmethod to-copresheaf NSet
  [^NSet nset]

  (let [coll (.colls nset)]
    (Copresheaf.
      (nth-discrete-category (count coll))
      (fn [n]
        (nth coll n))
      (fn [n]
        (identity-function (nth coll n))))))

(defmethod to-copresheaf MSet
  [^MSet ms]

  (Copresheaf.
    (.monoid ms)
    (fn [obj]
      (underlying-set ms))
    (fn [elem]
      (action-function ms elem))))

; Incidence structures as copresheaves
(defmethod to-copresheaf Span
  [span]

  (->Copresheaf
    incidence-category*
    (fn [obj]
      (cond
        (= obj "flags") (span-flags span)
        (= obj "lines") (span-edges span)
        (= obj "points") (span-vertices span)))
    (fn [arrow]
      (cond
        (= arrow "line") (edge-function span)
        (= arrow "point") (vertex-function span)
        (= arrow "1_points") (identity-function (span-vertices span))
        (= arrow "1_lines") (identity-function (span-edges span))
        (= arrow "1_flags") (identity-function (span-flags span))))))

; Create a triangle copresheaf from a pair of functions
(defn triangle-copresheaf
  [g f]

  (Copresheaf.
    triangle-category
    (fn [obj]
      (case obj
        "a" (inputs f)
        "b" (inputs g)
        "c" (outputs g)))
    (fn [arrow]
      (case arrow
        "1a" (identity-function (inputs f))
        "1b" (identity-function (inputs g))
        "1c" (identity-function (outputs g))
        "f" f
        "g" g
        "g ⚬ f" (compose g f)))))

; Morphisms of functions
(defmethod to-copresheaf Diamond
  [func]

  (let [id1 (intrinsic-identity-function? (first-function func))
        id2 (intrinsic-identity-function? (second-function func))]
    (cond
      (and id1 id2) (to-copresheaf (source-object func))
      id1 (triangle-copresheaf (second-function func) (source-object func))
      id2 (triangle-copresheaf (target-object func) (first-function func))

     :else
     (Copresheaf.
       diamond-category
       (fn [obj]
         (case obj
           "a" (inputs (source-object func))
           "b" (outputs (source-object func))
           "c" (inputs (target-object func))
           "d" (outputs (target-object func))))
       (fn [arrow]
         (case arrow
           "1a" (identity-function (inputs (source-object func)))
           "1b" (identity-function (outputs (source-object func)))
           "1c" (identity-function (inputs (target-object func)))
           "1d" (identity-function (outputs (target-object func)))
           "f" (source-object func)
           "g" (target-object func)
           "i" (input-set-function func)
           "o" (output-set-function func)
           "c" (compose (output-set-function func) (source-object func))))))))

; Morphisms of bijections
(defmethod to-copresheaf Gem
  [func]

  (let [s0 (inputs (source-object func))
        s1 (outputs (source-object func))
        s2 (inputs (target-object func))
        s3 (outputs (target-object func))]
    (Copresheaf.
     two-two-category
     (fn [obj]
       (case obj
         0 s0
         1 s1
         2 s2
         3 s3))
     (fn [arrow]
       (cond
         (= arrow '(0 0)) (identity-function s0)
         (= arrow '(1 1)) (identity-function s1)
         (= arrow '(0 1)) (underlying-function (source-object func))
         (= arrow '(1 0)) (underlying-function (inv (source-object func)))
         (= arrow '(2 2)) (identity-function s2)
         (= arrow '(3 3)) (identity-function s3)
         (= arrow '(2 3)) (underlying-function (target-object func))
         (= arrow '(3 2)) (underlying-function (inv (target-object func)))
         (= arrow '(0 2)) (first-function func)
         (= arrow '(0 3)) (compose (underlying-function (target-object func)) (first-function func))
         (= arrow '(1 2)) (compose (underlying-function (inv (target-object func))) (second-function func))
         (= arrow '(1 3)) (second-function func))))))

; Convert an nary function into a copresheaf
(defmethod to-copresheaf NFunction
  [^NFunction func]

  (let [funcs (.funcs func)
        arity (count funcs)]
    (letfn [(nth-set [obj]
              (if (even? obj)
                (inputs (nth funcs (/ obj 2)))
                (outputs (nth funcs (/ (dec obj) 2)))))]
      (Copresheaf.
        (n-pair-category arity)
        (fn [obj] (nth-set obj))
        (fn [[n m]]
          (if (= n m)
            (identity-function (nth-set n))
            (nth funcs (int (/ n 2)))))))))

(defmethod to-copresheaf Difunction
  [^Difunction difunc]

  (to-copresheaf (to-nfunction difunc)))

; Special classes of quivers
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

; Compositional quivers
(defn compositional-quiver-copresheaf
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
        "∘" (underlying-function category)
        "∘ source" (compose
                     (source-function category)
                     (underlying-function category))
        "∘ target" (compose
                     (target-function category)
                     (underlying-function category))))))

(defn compositional-unital-quiver-copresheaf
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
        "∘" (underlying-function category)
        "∘ source" (compose (source-function category) (underlying-function category))
        "∘ target" (compose (target-function category) (underlying-function category))
        "identity" (identity-element-function category)
        "idt" (source-identity-function category)
        "ids" (target-identity-function category)
        "∘ idt" (compose (target-identity-function category) (underlying-function category))
        "∘ ids" (compose (source-identity-function category) (underlying-function category))))))

(defn compositional-dependency-quiver-copresheaf
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
        "∘" (underlying-function category)
        "∘ source" (compose (source-function category) (underlying-function category))
        "∘ target" (compose (target-function category) (underlying-function category))
        "identity" (identity-element-function category)
        "idt" (source-identity-function category)
        "ids" (target-identity-function category)
        "∘ idt" (compose (target-identity-function category) (underlying-function category))
        "∘ ids" (compose (source-identity-function category) (underlying-function category))
        "reverse" (inverse-function category)
        "∘ reverse" (compose (inverse-function category) (underlying-function category))))))

(defmethod to-copresheaf :locus.elementary.function.core.protocols/semigroupoid
  [semigroupoid] (compositional-quiver-copresheaf semigroupoid))

(defmethod to-copresheaf :locus.elementary.function.core.protocols/category
  [category] (compositional-unital-quiver-copresheaf category))

(defmethod to-copresheaf :locus.elementary.function.core.protocols/groupoid
  [groupoid] (compositional-dependency-quiver-copresheaf groupoid))

; An nary-quiver is a generalisation of quivers for dealing with
; higher order nary-relations. In particular, there are ternary quivers
; which are the set valued functors which correspond most readily
; to ternary relations.
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

; Coprsheaves over finite total orders
(defn chain-copresheaf
  [& args]

  (let [funcs (reverse args)
        n (count funcs)]
    (letfn [(nth-set [i]
              (if (zero? i)
                (inputs (first funcs))
                (outputs (nth funcs (dec i)))))]
      (Copresheaf.
       (covering-generated-category (set (map seq (apply total-order (range (inc n))))))
       (fn [i] (nth-set i))
       (fn [[a b]]
         (if (= a b)
           (nth-set a)
           (apply
            compose
            (map
              (fn [i]
                (nth funcs i))
              (range a b)))))))))

; Create a cospan copresheaf
(defn cospan-copresheaf
  [first-source second-source target f g]

  (->Copresheaf
    two-cospan-category
    (fn [obj]
      (case obj
        "a" first-source
        "b" second-source
        "c" target))
    (fn [arrow]
      (case arrow
        "1a" (identity-function first-source)
        "1b" (identity-function second-source)
        "1c" (identity-function target)
        "f" f
        "g" g))))

(defn cospan-by-partition
  [func partition]

  (let [[a b] (seq partition)]
    (cospan-copresheaf
      a
      b
      (outputs func)
      (restrict-function func a)
      (restrict-function func b))))

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

; The singleton copresheaf naturally maps any object in a thin category
; to its corresponding singleton set with the unique arrows between them
(defn singleton-copresheaf
  [preorder]

  (Copresheaf.
    preorder
    (fn [obj]
      #{obj})
    (fn [arrow]
      (pair-function
        (source-element preorder arrow)
        (target-element preorder arrow)))))

; We need some way of dealing with functional dependencies
; This is only rudimentary at this stage of support and so it
; is due for a major refactoring involving the core system.
; and our basic notion of querying.
(defn induced-map
  [rel source target]

  (let [rval (apply
               merge
               (map
                 (fn [i]
                   {(restrict-list i source) (restrict-list i target)})
                 rel))]
    (if (nil? rval)
      {}
      rval)))

(defn induced-fn
  [rel source target]

  (fn [source-elements]
    (first
      (for [i rel
            :when (= (restrict-list i source) source-elements)]
        (restrict-list i target)))))

(defn induced-function
  [rel source target]

  (SetFunction.
    (project-relation rel source)
    (project-relation rel target)
    (induced-fn rel source target)))

(defn functional-dependencies-copresheaf
  [rel dep]

  (Copresheaf.
    (thin-category dep)
    (fn [nums]
      (project-relation rel nums))
    (fn [[source target]]
      (induced-function rel source target))))

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
        (cond
          (and (= objects-count 2) (= morphisms-count 2)) "DISET"
          (and (= objects-count 2) (= morphisms-count 3)) "FUNCTION"
          (and (= objects-count 2) (= morphisms-count 4)) "BIJECTION"
          (and (= objects-count 3) (n-span-category? index-category)) "INCIDENCE"
          (discrete-category? index-category) "NSET"
          (n-pair-category? index-category) "NFUNCTION"
          :else "COPRESHEAF")
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























