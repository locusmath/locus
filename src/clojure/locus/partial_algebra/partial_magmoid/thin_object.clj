(ns locus.partial-algebra.partial-magmoid.thin-object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.tree.two-quiver.core.object :refer :all]
            [locus.set.tree.two-quiver.path.object :refer :all]
            [locus.partial-algebra.partial-magmoid.object :refer :all])
  (:import (locus.set.copresheaf.two_quiver.path.object PathQuiver)))

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

(derive ThinPartialMagmoid :locus.set.copresheaf.structure.core.protocols/thin-partial-magmoid)

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




