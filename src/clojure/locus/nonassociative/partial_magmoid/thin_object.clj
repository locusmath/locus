(ns locus.nonassociative.partial-magmoid.thin-object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
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
            [locus.nonassociative.partial-magmoid.object :refer :all])
  (:import (locus.elementary.two_quiver.path.object PathQuiver)))

; A thin partial magmoid is an object in the category of partial magmoids that is fully
; determined by its underlying path quiver. So the functor from the category of partial
; magmoids to the topos of path quivers is an embedding of categories.
(deftype ThinPartialMagmoid [quiver paths]
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
  (invoke [this [[a b] [c d]]]
    (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive ThinPartialMagmoid :locus.elementary.copresheaf.core.protocols/thin-partial-magmoid)

; Paths of a thin partial magmoid
(defmethod paths ThinPartialMagmoid
  [^ThinPartialMagmoid magmoid]

  (.-paths magmoid))

(defmethod underlying-path-quiver ThinPartialMagmoid
  [^ThinPartialMagmoid magmoid]

  (->PathQuiver
    (paths magmoid)
    (morphisms magmoid)
    (objects magmoid)
    first
    second
    (source-fn magmoid)
    (target-fn magmoid)))

; Underlying relations
(defmethod underlying-relation ThinPartialMagmoid
  [^ThinPartialMagmoid magmoid]

  (underlying-relation (.-quiver magmoid)))

(defmethod underlying-multirelation ThinPartialMagmoid
  [^ThinPartialMagmoid magmoid]

  (underlying-multirelation (.-quiver magmoid)))

(defmethod visualize ThinPartialMagmoid
  [^ThinPartialMagmoid magmoid]

  (visualize (.-quiver magmoid)))

; Conversion mechanisms for thin partial magmoids
(defmulti to-thin-partial-magmoid type)

(defmethod to-thin-partial-magmoid ThinPartialMagmoid
  [^ThinPartialMagmoid magmoid] magmoid)

(defmethod to-thin-partial-magmoid PathQuiver
  [quiver]

  (ThinPartialMagmoid.
    (underlying-quiver quiver)
    (paths quiver)))

(defmethod to-thin-partial-magmoid :default
  [coll]

  (to-thin-partial-magmoid (to-path-quiver coll)))

; Products and coproducts in the category of partial magmoids
(defmethod coproduct ThinPartialMagmoid
  [& magmoids]

  (PartialMagmoid.
    (apply coproduct (map underlying-quiver magmoids))
    (apply sum-relation (map paths magmoids))))

(defmethod product ThinPartialMagmoid
  [& magmoids]

  (PartialMagmoid.
    (apply product (map underlying-quiver magmoids))
    (apply product-relation (map paths magmoids))))




