(ns locus.elementary.quiver.permutable.thin-object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]))

; Let C be the category consisting of the double arrow category, with an
; additional morphism on the edge objects for reversal that swaps the values
; of the two edges. Then Sets^C is the topos of permutable quivers. There is a
; natural induced functor from permutable quivers to quivers, and this leads
; to the related notion of a thin permutable quiver, which has an underlying thin
; component.

; A thin permutable quiver is then precisely equivalent to a symmetric relation,
; which in turn is equivalent to an undirected graph. As a consequence, this is the basic
; manner that undirected graphs can be integrated into our topos theoretic framework.
; Our ontology is equipped via multimethods to handle thin permutable quivers as special
; cases of objects of a topos.
(deftype ThinPermutableQuiver [vertices edges]
  ; structure over the topos of sets
  ConcreteObject
  (underlying-set [this] vertices)

  ; structure over the topos of pairs of sets
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] this)
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredPermutableQuiver
  (underlying-permutable-quiver [this] this)
  (invert-morphism [this morphism] (reverse morphism)))

(derive ThinPermutableQuiver :locus.elementary.quiver.permutable.object/thin-permutable-quiver)

; Constructor for thin permutable quivers
(defn thin-permutable-quiver
  ([rel]
   (thin-permutable-quiver (vertices rel) rel))
  ([coll rel]
   (ThinPermutableQuiver. coll rel)))

(defn thin-permutable-quiver-component
  [quiver]

  (ThinPermutableQuiver. (objects quiver) (underlying-relation quiver)))

; Complement a thin permutable quiver
(defn complement-thin-permutable-quiver
  [quiv]

  (ThinPermutableQuiver.
    (objects quiv)
    (difference
      (cartesian-power (objects quiv) 2)
      (underlying-relation quiv))))

; Get the underlying relation of a thin permutable quiver
(defmethod underlying-relation ThinPermutableQuiver
  [^ThinPermutableQuiver quiv]

  (.edges quiv))

(defmethod visualize ThinPermutableQuiver
  [^ThinPermutableQuiver quiv]

  (visualize (.edges quiv)))

; Products and coproducts in the topos of permutable quivers
(defmethod product ThinPermutableQuiver
  [& quivers]

  (ThinPermutableQuiver.
    (apply cartesian-product (map objects quivers))
    (apply product-relation (map morphisms quivers))))

(defmethod coproduct ThinPermutableQuiver
  [& quivers]

  (ThinPermutableQuiver.
    (apply cartesian-product (map objects quivers))
    (apply product-relation (map morphisms quivers))))