(ns locus.grothendieck.site.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.topology.core.object :refer :all])
  (:import (locus.topology.core.object TopologicalSpace)))

; Sites are the fundamental index categories of Grothendieck toposes.
; A site is equipped with a coverage cov : Ob(C) -> CoveringFamilies.
; This function cov maps any object to a family of common output morphism
; systems, which can be defined to be a predicate on the power class of the
; morphisms collection of the category. In particular, we can define sites
; from topological spaces.
(deftype Site [morphisms objects source target func id coverage]
  ; Categories are structured quivers
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  ; Categories are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Site :locus.elementary.copresheaf.core.protocols/structured-category)

(defmethod to-category Site
  [^Site site]

  (->Category
    (->UnitalQuiver
      (morphisms site)
      (objects site)
      (source-fn site)
      (target-fn site)
      (.id site))
    (.func site)))

; A site is generally speaking a generalisation of a topological space, which
; is useful for applications in sheaf theory. So one of the most important things
; that we need to implement is a function that takes a topological space, represented
; by its family of open sets and which turns it into a site.
(defn topological-site
  ([family]
   (topological-site (apply union family) family))
  ([coll family]
   (Site.
     (inclusion-relation family)
     family
     first
     second
     compose-ordered-pairs
     (fn [x] (list x x))
     (fn [open-set]
       (fn [coll]
         (= (apply union (map first coll)) open-set))))))

; Conversions of topological spaces into sites
(defmulti to-site type)

(defmethod to-site TopologicalSpace
  [^TopologicalSpace topology]

  (topological-site
    (underlying-set topology)
    (.opens topology)))

(defmethod to-site :default
  [coll] (topological-site coll))

; A discrete site is simply a special case of the idea of a topological site, but over
; a discrete topological space. It is important because it helps us to define some
; of the most basic concepts of site theory. In a sense it is really just an ordinary
; set upon which we can define sheaves.
(defn discrete-site
  [coll]

  (topological-site (power-set coll)))

(defn indiscrete-site
  [coll]

  (topological-site (set (list #{} coll))))

; add a covarage to an existing category
(defn adjoin-coverage
  [category coverage]

  (Site.
    (morphisms category)
    (objects category)
    (source-fn category)
    (target-fn category)
    (.func category)
    (.id category)
    coverage))

; Ontology of sites
; A site is an object upon which a Grothendieck topos is born. On the other hand,
; an elementary category is an object upon which elementary topoi is constructed. These
; are the two main settings that topos theory are done on. Therefore, we call any category
; that isn't a site, and that therefore doesn't have a covering an elementary category
; because its corresponding topos is an elementary topos.
(defn site?
  [category]

  (= (type category) Site))

(defn elementary-category?
  [category]

  (and
    (category? category)
    (not (site? category))))



