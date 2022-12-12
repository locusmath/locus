(ns locus.set.quiver.binary.algebraic.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.effects.global.transformation :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.partial.mapping.transformation :refer :all]))

; An algebraic binary quiver is a presheaf F: T_{2,2} -> Sets in which the first of the two output
; functions of the parallel arrows in the index category T_{2,2} is injective. The fact that
; one of the two components is injective, then determines that the quiver is thin and the
; morphism components of an edge of the quiver can be fully determined by its first part. The
; result is that an algebraic binary quiver is essentially equivalent to a partial transformation.

(deftype ABQuiver [in out func]
  StructuredDiset
  (first-set [this] in)
  (second-set [this] out)

  StructuredQuiver
  (source-fn [this] identity)
  (target-fn [this] func)
  (transition [this e] (list e (func e)))
  (underlying-quiver [this] this))

(derive ABQuiver :locus.set.quiver.structure.core.protocols/thin-quiver)

; Underlying relations of algebraic binary quivers
(defmethod underlying-relation ABQuiver
  [^ABQuiver quiver]

  (let [func (.-func quiver)]
    (set
      (map
        (fn [morphism]
          (list morphism (func morphism)))
        (morphisms quiver)))))

(defmethod underlying-multirelation ABQuiver
  [^ABQuiver quiver] (underlying-relation quiver))

(defmethod visualize ABQuiver
  [^ABQuiver quiver]

  (visualize (underlying-relation quiver)))

; Algebraic binary quivers are essentially equivalent to partial transformations
(defmethod to-partial-transformation ABQuiver
  [^ABQuiver quiver]

  (->PartialTransformation
    (.-in quiver)
    (.-out quiver)
    (.-func quiver)))

; Methods to convert partial transformations and other objects into algebraic quivers
(defmulti to-algebraic-binary-quiver type)

(defmethod to-algebraic-binary-quiver ABQuiver
  [^ABQuiver quiver] quiver)

(defmethod to-algebraic-binary-quiver :locus.partial.mapping.function/partial-transformation
  [transformation]

  (ABQuiver.
    (defined-domain transformation)
    (source-object transformation)
    (fn [i]
      (transformation i))))

(defmethod to-algebraic-binary-quiver :locus.set.logic.structure.protocols/transformation
  [func]

  (ABQuiver.
    (source-object func)
    (target-object func)
    func))

(defmethod to-algebraic-binary-quiver :locus.set.logic.core.set/universal
  [rel]

  (let [[in out func] (loop [coll (seq rel)
                             in #{}
                             out #{}
                             func {}]
                        (if (empty? coll)
                          [in out func]
                          (let [[a b] (first coll)]
                            (recur
                              (rest coll)
                              (conj in a)
                              (conj out a b)
                              (conj func [a b])))))]
    (ABQuiver. in out func)))
