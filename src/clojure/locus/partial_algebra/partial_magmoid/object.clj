(ns locus.partial-algebra.partial-magmoid.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.thin.object :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.partial-algebra.partial-magma.object :refer :all])
  (:import (locus.partial_algebra.partial_magma.object PartialMagma)))

; A partial magmoid is any partial composition operation on a quiver. They include
; magmoids, semigroupoids, categories, groupoids, and others as special cases.
; They are the horizontal categorification of partial algebra.
(deftype PartialMagmoid [quiver paths op]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] quiver)
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  ConcreteMorphism
  (inputs [this] paths)
  (outputs [this] (morphisms quiver))

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PartialMagmoid :locus.elementary.copresheaf.core.protocols/partial-magmoid)

; An accessor function for the underlying path set of a partial magmoid
(defmethod paths PartialMagmoid
  [^PartialMagmoid magmoid]

  (.-paths magmoid))

; There exists a functor from the category of partial magmoids to the topos of path quivers
(defmethod underlying-path-quiver PartialMagmoid
  [^PartialMagmoid magmoid]

  (->PathQuiver
    (paths magmoid)
    (morphisms magmoid)
    (objects magmoid)
    first
    second
    (source-fn magmoid)
    (target-fn magmoid)))

; A magmoid is a partial magmoid with a full underlying compositional path quiver
(defmethod magmoid? :locus.elementary.copresheaf.core.protocols/partial-magmoid
  [magmoid]

  (let [paths (paths magmoid)]
    (every?
     (fn [pair]
       (paths pair))
     (composability-relation magmoid))))

(defmethod thin-partial-magmoid? :locus.elementary.copresheaf.core.protocols/partial-magmoid
  [magmoid]

  (thin-quiver? (underlying-quiver magmoid)))

; Underlying relations and multirelations for partial magmoids
(defmethod underlying-relation PartialMagmoid
  [^PartialMagmoid magmoid]

  (underlying-relation (.-quiver magmoid)))

(defmethod underlying-multirelation PartialMagmoid
  [^PartialMagmoid magmoid]

  (underlying-multirelation (.-quiver magmoid)))

(defmethod visualize PartialMagmoid
  [^PartialMagmoid magmoid]

  (visualize (.-quiver magmoid)))

; Convert various algebraic structures into partial magmoids
(defmulti to-partial-magmoid type)

(defmethod to-partial-magmoid PartialMagmoid
  [^PartialMagmoid magmoid] magmoid)

(defmethod to-partial-magmoid PartialMagma
  [^PartialMagma magma]

  (->PartialMagmoid
    (underlying-quiver magma)
    (.-rel magma)
    (.-op magma)))

; Products and coproducts in the category of partial magmoids
(defmethod coproduct PartialMagmoid
  [& magmoids]

  (PartialMagmoid.
    (apply coproduct (map underlying-quiver magmoids))
    (apply sum-relation (map paths magmoids))
    (fn [[[i v] [j w]]]
      (list i ((nth magmoids i) (list v w))))))

(defmethod product PartialMagmoid
  [& magmoids]

  (PartialMagmoid.
    (apply product (map underlying-quiver magmoids))
    (apply product-relation (map paths magmoids))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i magmoid]
          (magmoid (list (nth morphisms1 i) (nth morphisms2 i))))
        magmoids))))

; The dual of partial magmoids
(defmethod dual PartialMagmoid
  [magmoid]

  (PartialMagmoid.
    (dual (underlying-quiver magmoid))
    (transpose (paths magmoid))
    (comp magmoid reverse)))

; Subobjects in the category of magmoids
; Unlike in the simpler case of categories, we see that a partial magmoid is a copresheaf
; on there sets rather than two. Therefore, in order to get a subobject of a partial magmoid,
; you can reduce not only its set of objects and morphisms, but also its compositional domain.
(defn partial-submagmoid?
  [magmoid new-paths new-edges new-objects]

  (let [quiv (underlying-quiver magmoid)]
    (and
      (subquiver? quiv new-edges new-objects)
      (every?
        (fn [path]
          (and
            (boolean (new-edges (first path)))
            (boolean (new-edges (second path)))
            (boolean (new-edges (magmoid path)))))
        new-paths))))

(defn partial-submagmoid
  [magmoid new-paths new-edges new-objects]

  (PartialMagmoid.
    (subquiver (underlying-quiver magmoid) new-edges new-objects)
    new-paths
    magmoid))

(defn restrict-partial-magmoid
  [magmoid new-paths]

  (PartialMagmoid. (underlying-quiver magmoid) new-paths magmoid))

(defn domain-full-partial-submagmoid
  [magmoid new-edges new-objects]

  (let [new-paths (filter
                    (fn [path]
                      (and
                        (boolean (new-edges (first path)))
                        (boolean (new-edges (second path)))))
                    (paths magmoid))]
    (partial-submagmoid magmoid new-paths new-edges new-objects)))

(defn wide-partial-submagmoid
  [magmoid new-edges]

  (domain-full-partial-submagmoid magmoid new-edges (objects magmoid)))

(defn full-partial-submagmoid
  [magmoid new-objects]

  (let [quiv (underlying-quiver magmoid)
        new-edges (quiver-set-inverse-image quiv new-objects)]
    (domain-full-partial-submagmoid magmoid new-edges new-objects)))

; Get a quotient partial magmoid from a partial magmoid and a compositional congruence.
; This can be used to get the quotients of the congruences of a category, which need not
; remain within the category of categories. So we can use the category of partial magmoids
; instead in order to study categorical congruences.
(defn quotient-partial-magmoid
  [magmoid in-partition out-partition]

  (PartialMagmoid.
    (quotient-quiver (underlying-quiver magmoid) in-partition out-partition)
    (partition-set-by-function
      (fn [[a b]]
        (list (projection in-partition a) (projection in-partition b)))
      (paths magmoid))
    (fn [[a b]]
      (projection
        in-partition
        (magmoid (list (first a) (first b)))))))
