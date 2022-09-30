(ns locus.elementary.triangle.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]))

; Objects of the elementary topos Sets^(T_3) of copresheaves over the total
; order with three elements. These can be formed from copresheaves in the
; fundamental topos Sets^[1,2,1] in two different ways.
(deftype TriangleCopresheaf [f g]
  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct
      [(inputs g)
       (outputs g)
       (outputs f)])))

(derive TriangleCopresheaf :locus.base.logic.structure.protocols/structured-set)

; Convert a relation into a triangle copresheaf
(defn relation-to-triangle
  [rel]

  (->TriangleCopresheaf
    (relation-transition-map rel 1 2)
    (relation-transition-map rel 0 1)))

; Generalized conversion methods
(defmulti to-triangle-copresheaf type)

(defmethod to-triangle-copresheaf TriangleCopresheaf
  [^TriangleCopresheaf triangle] triangle)

(defmethod to-triangle-copresheaf :locus.base.logic.core.set/universal
  [rel] (relation-to-triangle rel))

; The underlying relations of triangle copresheaves
(defmethod underlying-relation TriangleCopresheaf
  [^TriangleCopresheaf triangle]

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

(defmethod underlying-multirelation TriangleCopresheaf
  [triangle] (underlying-relation triangle))

; Function components of triangles
(defn prefunction
  [^TriangleCopresheaf triangle]

  (.g triangle))

(defn postfunction
  [^TriangleCopresheaf triangle]

  (.f triangle))

(defn compfunction
  [^TriangleCopresheaf triangle]

  (compose (.f triangle) (.g triangle)))

(defn triangle-component-functions
  [^TriangleCopresheaf triangle]

  (list (.-f triangle) (.-g triangle)))

; Set components of triangles
(defn triangle-source
  [^TriangleCopresheaf triangle]

  (source-object (prefunction triangle)))

(defn triangle-middle
  [^TriangleCopresheaf triangle]

  (target-object (prefunction triangle)))

(defn triangle-target
  [^TriangleCopresheaf triangle]

  (target-object (postfunction triangle)))

(defn triangle-component-sets
  [^TriangleCopresheaf triangle]

  (list (triangle-target triangle) (triangle-middle triangle) (triangle-source triangle)))

; Get the kernels of the triangle
(defn triangle-source-kernels
  [^TriangleCopresheaf triangle]

  (list
    (function-kernel (prefunction triangle))
    (function-kernel (compfunction triangle))))

(defn triangle-target-images
  [^TriangleCopresheaf triangle]

  (list
    (function-image (postfunction triangle))
    (function-image (compfunction triangle))))

; Special types of triangle copresheaves
(defn trivial-triangle
  [coll]

  (TriangleCopresheaf. (identity-function coll) (identity-function coll)))

(defn prefunction-trivial-triangle
  [func]

  (TriangleCopresheaf. func (identity-function (source-object func))))

(defn postfunction-trivial-triangle
  [func]

  (TriangleCopresheaf. (identity-function (target-object func)) func))

; An ordered triple as a triangle copresheaf
(defn triple-triangle
  [a b c]

  (->TriangleCopresheaf
    (pair-function b c)
    (pair-function a b)))

(defn inclusion-triangle
  [a b c]

  (->TriangleCopresheaf
    (inclusion-function b c)
    (inclusion-function a b)))

; Products and coproducts in the topoi of triangle copresheaves
(defn triangle-product
  [& args]

  (TriangleCopresheaf.
    (apply product (map postfunction args))
    (apply product (map prefunction args))))

(defn triangle-coproduct
  [& args]

  (TriangleCopresheaf.
    (apply coproduct (map postfunction args))
    (apply coproduct (map prefunction args))))

(defmethod product TriangleCopresheaf
  [& args]

  (apply triangle-product args))

(defmethod coproduct TriangleCopresheaf
  [& args]

  (apply triangle-coproduct args))

; Compute the substructure of a triangle copresheaf
(defn subtriangle?
  [triangle new-source new-middle new-target]

  (and
    (subfunction? (postfunction triangle) new-middle new-target)
    (subfunction? (prefunction triangle) new-source new-middle)))

(defn subtriangle
  [triangle new-source new-middle new-target]

  (TriangleCopresheaf.
    (subfunction (postfunction triangle) new-middle new-target)
    (subfunction (prefunction triangle) new-source new-middle)))

(defn restrict-triangle-source
  [triangle new-source]

  (TriangleCopresheaf.
    (postfunction triangle)
    (restrict-function (prefunction triangle) new-source)))

; Compute the quotients of a triangle copresheaf
(defn triangle-congruence?
  [triangle source-partition middle-partition target-partition]

  (and
    (io-relation? (postfunction triangle) middle-partition target-partition)
    (io-relation? (prefunction triangle) source-partition middle-partition)))

(defn quotient-triangle
  [triangle source-partition middle-partition target-partition]

  (TriangleCopresheaf.
    (quotient-function (postfunction triangle) middle-partition target-partition)
    (quotient-function (prefunction triangle) source-partition middle-partition)))

; Ontology of triangle copresheaves
(defn triangle?
  [x]

  (= (type x) TriangleCopresheaf))

(defn prefunction-invertible-triangle?
  [x]

  (and
    (triangle? x)
    (invertible? (prefunction x))))

(defn postfunction-invertible-triangle?
  [x]

  (and
    (triangle? x)
    (invertible? (postfunction x))))

(defn invertible-triangle?
  [x]

  (and
    (triangle? x)
    (invertible? (prefunction x))
    (invertible? (postfunction x))))

; Identity functions are special cases of invertible ones
(defn prefunction-trivial-triangle?
  [x]

  (and
    (triangle? x)
    (identity-function? (prefunction x))))

(defn postfunction-trivial-triangle?
  [x]

  (and
    (triangle? x)
    (identity-function? (postfunction x))))

(defn trivial-triangle?
  [x]

  (and
    (triangle? x)
    (identity-function? (prefunction x))
    (identity-function? (postfunction x))))

; Triangles are nicely visualizable
(defmethod visualize TriangleCopresheaf
  [^TriangleCopresheaf triangle]

  (let [[p v] (generate-copresheaf-data
                {0 (triangle-source triangle)
                 1 (triangle-middle triangle)
                 2 (triangle-target triangle)}
                #{(list 0 1 (prefunction triangle))
                  (list 1 2 (postfunction triangle))})]
    (visualize-clustered-digraph* "LR" p v)))
