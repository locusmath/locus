(ns locus.elementary.triangle.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.bijection.core.object :refer :all]))

; Objects of the elementary topos Sets^(T_3) of copresheaves over the total
; order with three elements. These can be formed from copresheaves in the
; fundamental topos Sets^[1,2,1] in two different ways. Triangle copresheaves
; are equivalent to composable pairs in the topos Sets of sets and functions.
; This file implements triangle copresheaves in terms of such composable
; pairs of functions, and it provides all their relevant presheaf
; theoretic functionality.

(deftype SetTriangle [f g]
  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct
      [(inputs g)
       (outputs g)
       (outputs f)])))

(derive SetTriangle :locus.base.logic.structure.protocols/structured-set)

; Triangle components
(defn triangle-source
  [^SetTriangle triangle]

  (inputs (.-g triangle)))

(defn triangle-middle
  [^SetTriangle triangle]

  (outputs (.-g triangle)))

(defn triangle-target
  [^SetTriangle triangle]

  (outputs (.-f triangle)))

(defn prefunction
  [^SetTriangle triangle]

  (.-g triangle))

(defn postfunction
  [^SetTriangle triangle]

  (.-f triangle))

(defn compfunction
  [^SetTriangle triangle]

  (compose (.-f triangle) (.-g triangle)))

; Components of triangles
(defmethod get-set SetTriangle
  [^SetTriangle triangle, x]

  (case x
    0 (triangle-source triangle)
    1 (triangle-middle triangle)
    2 (triangle-target triangle)))

(defmethod get-function SetTriangle
  [^SetTriangle triangle, [a b]]

  (case [a b]
    [0 0] (identity-function (triangle-source triangle))
    [1 1] (identity-function (triangle-middle triangle))
    [2 2] (identity-function (triangle-target triangle))
    [0 1] (prefunction triangle)
    [0 2] (compfunction triangle)
    [1 2] (postfunction triangle)))

; The underlying relations of triangles
(defmethod underlying-relation SetTriangle
  [^SetTriangle triangle]

  (let [prefunction (.-g triangle)
        postfunction (.-f triangle)]
    (set
      (map
        (fn [input]
          (list
            input
            (prefunction input)
            (postfunction (prefunction input))))
        (inputs prefunction)))))

(defmethod underlying-multirelation SetTriangle
  [triangle] (underlying-relation triangle))

; Generalized conversion mechanisms
(defn relation-to-triangle
  [rel]

  (->SetTriangle
    (relation-transition-map rel 1 2)
    (relation-transition-map rel 0 1)))

(defmulti to-triangle type)

(defmethod to-triangle SetTriangle
  [^SetTriangle triangle] triangle)

(defmethod to-triangle :locus.base.logic.core.set/universal
  [rel] (relation-to-triangle rel))

(defmethod to-triangle :locus.elementary.copresheaf.core.protocols/bijection
  [bijection]

  (->SetTriangle
    (underlying-function (inv bijection))
    (underlying-function bijection)))

; Special types of triangles
(defn constant-triangle
  [coll]

  (SetTriangle. (identity-function coll) (identity-function coll)))

(defn prefunction-trivial-triangle
  [func]

  (SetTriangle. func (identity-function (source-object func))))

(defn postfunction-trivial-triangle
  [func]

  (SetTriangle. (identity-function (target-object func)) func))

(defn triple-triangle
  [a b c]

  (->SetTriangle
    (pair-function b c)
    (pair-function a b)))

(defn inclusion-triangle
  [a b c]

  (->SetTriangle
    (inclusion-function b c)
    (inclusion-function a b)))

; Triangle component sets and functions
(defn triangle-component-sets
  [^SetTriangle triangle]

  (list
    (triangle-source triangle)
    (triangle-middle triangle)
    (triangle-target triangle)))

(defn triangle-component-functions
  [^SetTriangle triangle]

  (list (.-f triangle) (.-g triangle)))

; Get the kernels of the triangle
(defn triangle-source-kernels
  [^SetTriangle triangle]

  (list
    (function-kernel (prefunction triangle))
    (function-kernel (compfunction triangle))))

(defn triangle-target-images
  [^SetTriangle triangle]

  (list
    (function-image (postfunction triangle))
    (function-image (compfunction triangle))))

; Products and coproducts in the topos of triangles
(defn triangle-product
  [& args]

  (SetTriangle.
    (apply product (map postfunction args))
    (apply product (map prefunction args))))

(defn triangle-coproduct
  [& args]

  (SetTriangle.
    (apply coproduct (map postfunction args))
    (apply coproduct (map prefunction args))))

(defmethod product SetTriangle
  [& args]

  (apply triangle-product args))

(defmethod coproduct SetTriangle
  [& args]

  (apply triangle-coproduct args))

; Subobjects in the topos of triangles
(defn subtriangle
  [triangle new-source new-middle new-target]

  (SetTriangle.
    (subfunction (postfunction triangle) new-middle new-target)
    (subfunction (prefunction triangle) new-source new-middle)))

(defn restrict-triangle-source
  [triangle new-source]

  (SetTriangle.
    (postfunction triangle)
    (restrict-function (prefunction triangle) new-source)))

(defn reduce-prefunction
  [triangle new-source new-middle]

  (SetTriangle.
    (postfunction triangle)
    (subfunction (prefunction triangle) new-source new-middle)))

; Testing for subobjects of triangles
(defn subtriangle?
  [triangle new-source new-middle new-target]

  (and
    (subfunction? (postfunction triangle) new-middle new-target)
    (subfunction? (prefunction triangle) new-source new-middle)))

(defn subtriangle-closure
  [triangle new-source new-middle new-target]

  (let [closed-middle (union new-middle (set-image (prefunction triangle) new-source))
        closed-target (union new-target (set-image (postfunction triangle) closed-middle))]
    (list new-source closed-middle closed-target)))

; Enumeration theory for triangles
(defn ^{:private true} subtriangles-by-input-set
  [triangle input-set]

  (let [minimal-middle-set (set-image
                             (prefunction triangle)
                             input-set)
        remaining-middle-elements (difference
                                    (triangle-middle triangle)
                                    minimal-middle-set)]
    (mapcat
      (fn [middle-additions]
        (let [current-middle-set (union minimal-middle-set middle-additions)
              minimal-target-set (set-image
                                   (postfunction triangle)
                                   current-middle-set)
              remaining-target-elements (difference
                                          (triangle-target triangle)
                                          minimal-target-set)]
          (map
            (fn [target-additions]
              (let [current-target-set (union minimal-target-set target-additions)]
                (list
                  input-set
                  current-middle-set
                  current-target-set)))
            (power-set remaining-target-elements))))
      (power-set remaining-middle-elements))))

(defn subtriangles
  [triangle]

  (set
    (mapcat
      (fn [input-set]
        (subtriangles-by-input-set triangle input-set))
      (power-set (triangle-source triangle)))))

; Relations on the subtriangles of a triangle
(defn covering-subtriangles
  [triangle source middle target]

  (let [pref (prefunction triangle)
        postf (postfunction triangle)]
    (set
     (concat
       (let [source-additions (set
                                (filter
                                  (fn [i]
                                    (contains? middle (pref i)))
                                  (difference (triangle-source triangle) source)))]
         (map
           (fn [i]
             (list (conj source i) middle target))
           source-additions))
       (let [middle-additions (set
                                (filter
                                  (fn [i]
                                    (contains? target (postf i)))
                                  (difference (triangle-middle triangle) middle)))]
         (map
           (fn [i]
             (list source (conj middle i) target))
           middle-additions))
       (let [target-additions (difference (triangle-target triangle) target)]
         (map
           (fn [i]
             (list source middle (conj target i)))
           target-additions))))))

(defn subtriangles-covering
  [triangle]

  (set
    (mapcat
      (fn [[a b c]]
        (map
          (fn [[x y z]]
            (list (list a b c) (list x y z)))
          (covering-subtriangles triangle a b c)))
      (subtriangles triangle))))

; Quotients in the topos of triangles
(defn quotient-triangle
  [triangle source-partition middle-partition target-partition]

  (SetTriangle.
    (quotient-function (postfunction triangle) middle-partition target-partition)
    (quotient-function (prefunction triangle) source-partition middle-partition)))

; Compute the quotients of a triangle copresheaf
(defn triangle-congruence?
  [triangle source-partition middle-partition target-partition]

  (and
    (io-relation? (postfunction triangle) middle-partition target-partition)
    (io-relation? (prefunction triangle) source-partition middle-partition)))

(defn triangle-congruence-closure
  [triangle source-partition middle-partition target-partition]

  (let [closed-middle-partition (join-set-partitions
                                  middle-partition
                                  (partition-image
                                    (prefunction triangle)
                                    source-partition))
        closed-target-partition (join-set-partitions
                                  target-partition
                                  (partition-image
                                    (postfunction triangle)
                                    closed-middle-partition))]
    (list source-partition closed-middle-partition closed-target-partition)))

; Enumeration of all congruences of a triangle copresheaf
(defn ^{:private true} triangle-congruences-by-input-partition
  [triangle in-partition]

  (let [minimal-middle-partition (partition-image (prefunction triangle) in-partition)]
    (mapcat
      (fn [current-middle-partition]
        (let [minimal-target-partition (partition-image (postfunction triangle) current-middle-partition)]
          (map
            (fn [current-target-partition]
              (list in-partition current-middle-partition current-target-partition))
            (set-partition-coarsifications minimal-middle-partition))))
      (set-partition-coarsifications minimal-middle-partition))))

(defn triangle-congruences
  [triangle]

  (set
    (mapcat
      (fn [in-partition]
        (triangle-congruences-by-input-partition triangle in-partition))
      (enumerate-set-partitions (triangle-source triangle)))))

; The covering relation on the congruence lattice of a triangle copresheaf
(defn triangle-covering-congruences
  [triangle source-partition middle-partition target-partition]

  (let [prefunc (prefunction triangle)
        postfunc (postfunction triangle)
        compfunc (compfunction triangle)]
    (set
      (concat
        (for [i (direct-set-partition-coarsifications source-partition)
              :when (and
                      (set-superpartition?
                       (list (partition-image prefunc i) middle-partition))
                      (set-superpartition?
                        (list (partition-image compfunc i) target-partition)))]
          (list i middle-partition target-partition))
        (for [i (direct-set-partition-coarsifications middle-partition)
              :when (set-superpartition?
                      (list (partition-image postfunc i) target-partition))]
          (list source-partition i target-partition))
        (for [i (direct-set-partition-coarsifications target-partition)]
          (list source-partition middle-partition i))))))

(defn triangle-congruences-covering
  [triangle]

  (set
    (mapcat
      (fn [[p q r]]
        (map
          (fn [[new-p new-q new-r]]
            (list [p q r] [new-p new-q new-r]))
          (triangle-covering-congruences triangle p q r)))
      (triangle-congruences triangle))))

; Ontology of triangle copresheaves
(defn set-triangle?
  [x]

  (= (type x) SetTriangle))

(defn prefunction-endo-triangle?
  [x]

  (and
    (set-triangle? x)
    (endofunction? (prefunction x))))

(defn postfunction-endo-triangle?
  [x]

  (and
    (set-triangle? x)
    (endofunction? (postfunction x))))

(defn composition-endo-triangle?
  [x]

  (and
    (set-triangle? x)
    (endofunction? (compfunction x))))

(defn prefunction-trivial-triangle?
  [x]

  (and
    (set-triangle? x)
    (identity-function? (prefunction x))))

(defn postfunction-trivial-triangle?
  [x]

  (and
    (set-triangle? x)
    (identity-function? (postfunction x))))

(defn composition-trivial-triangle?
  [x]

  (and
    (set-triangle? x)
    (identity-function? (compfunction x))))

(defn trivial-triangle?
  [x]

  (and
    (set-triangle? x)
    (identity-function? (prefunction x))
    (identity-function? (postfunction x))))

; Classes of triangles by invertibility and related conditions
(defn prefunction-invertible-triangle?
  [x]

  (and
    (set-triangle? x)
    (invertible? (prefunction x))))

(defn postfunction-invertible-triangle?
  [x]

  (and
    (set-triangle? x)
    (invertible? (postfunction x))))

(defn invertible-triangle?
  [x]

  (and
    (set-triangle? x)
    (invertible? (prefunction x))
    (invertible? (postfunction x))))

; Triangles are nicely visualizable
(defmethod visualize SetTriangle
  [^SetTriangle triangle]

  (let [[p v] (generate-copresheaf-data
                {0 (triangle-source triangle)
                 1 (triangle-middle triangle)
                 2 (triangle-target triangle)}
                #{(list 0 1 (prefunction triangle))
                  (list 1 2 (postfunction triangle))})]
    (visualize-clustered-digraph* "LR" p v)))