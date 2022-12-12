(ns locus.set.tree.two-quiver.globular.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all]
            [locus.set.tree.two-quiver.core.object :refer :all]))

; Two globular sets are the first model in the topos theory of higher categories, starting with
; two categories which are modeled over two globular sets. Specifically, a two globular
; set is simply a quiver Q for which each hom class Hom(a,b) in the quiver is itself
; a quiver. So we can speak of the hom quivers of the two globular set. Abstracting from
; this a two category has a category for any hom class, which in turn has its own
; underlying quiver in the same way that any two category has its own underlying
; two globular sets. These are the first in a series of higher categorical constructions
; that generalise quivers to other goemetric shapes for higher categories.
(deftype TwoGlobularSet [two-morphisms morphisms objects two-source two-target source target]
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [two-morphisms morphisms objects]))

  StructuredQuiver
  (underlying-quiver [this]
    (->Quiver
      morphisms
      objects
      source
      target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e]
    (list (source e) (target e)))

  StructuredTwoQuiver
  (two-morphisms [this] two-morphisms)
  (two-source-fn [this] two-source)
  (two-target-fn [this] two-target))

(derive TwoGlobularSet :locus.set.tree.two-quiver.core.object/two-quiver)

; A mechanism for visualizing two globular sets
; In order to visualize two globular sets all you need to do is look at their underlying quivers
(defmethod visualize TwoGlobularSet
  [^TwoGlobularSet globe]

  (visualize (underlying-quiver globe)))

; The distinguishing property of two globular sets is that they have hom quivers for each of their
; hom classes Hom(a,b) which are used as models of two categories and bicategories in higher
; category theory and related fields.
(defn hom-quiver
  [quiver a b]

  (->Quiver
    (two-hom quiver a b)
    (quiver-hom-class quiver a b)
    (two-source-fn quiver)
    (two-target-fn quiver)))

; A constructor for two globular sets
(defn two-gs
  [vertices hom]

  (let [underlying-hom-map (into
                             {}
                             (map
                               (fn [[key quiver]]
                                 [key (objects quiver)])
                               hom))
        quiver (make-quiver vertices underlying-hom-map)
        quivers (vals hom)
        two-morphisms (apply union (map morphisms quivers))
        two-source (apply
                     merge
                     (map quiver-source-map quivers))
        two-target (apply
                     merge
                     (map quiver-target-map quivers))]
    (->TwoGlobularSet
      two-morphisms
      (morphisms quiver)
      (objects quiver)
      two-source
      two-target
      (source-fn quiver)
      (target-fn quiver))))

(def exgs
  (two-gs
    #{0 1 2 3}
    {(list 0 1) (to-quiver (mapfn {:x 1, :y 2}))
     (list 1 2) (to-quiver (mapfn {:a 3, :b 4}))}))

; Ontology of two globular sets
(defn two-globular-set?
  [two-quiver]

  (= (type two-quiver) TwoGlobularSet))
