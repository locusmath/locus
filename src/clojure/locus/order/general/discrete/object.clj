(ns locus.order.general.discrete.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.copresheaf.quiver.dependency.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; A discrete category is a way of representing each set as a category. In this way, there exists
; an embedding functor F: Sets -> Cat that embeds the topos of Sets into the category of all
; categories, using discrete posets and functors as the objects and morphisms of the
; embedding.

(deftype DiscretePoset [coll]
  ConcreteObject
  (underlying-set [this] coll)

  StructuredDiset
  (first-set [this] (coreflexive-relation coll))
  (second-set [this] coll)

  StructuredQuiver
  (underlying-quiver [this] (coreflexive-relational-quiver coll))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (identity-morphism-of [this x] (list x x))
  (underlying-unital-quiver [this] (coreflexive-relational-unital-quiver coll))

  StructuredPermutableQuiver
  (invert-morphism [this x] (reverse x))
  (underlying-permutable-quiver [this] (coreflexive-relational-permutable-quiver coll))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this] (coreflexive-relational-dependency-quiver coll))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (first-set this))

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive DiscretePoset :locus.set.copresheaf.structure.core.protocols/thin-skeletal-category)

; Generalized conversion routines so that we can treat sets like they are discrete categories
(defmulti to-discrete-category type)

(defmethod to-discrete-category DiscretePoset
  [poset] poset)

(defmethod to-discrete-category :locus.set.logic.core.set/universal
  [coll]

  (->DiscretePoset coll))

; Underlying relations of discrete categories
(defmethod underlying-relation DiscretePoset
  [^DiscretePoset coll] (coreflexive-relation (.-coll coll)))

(defmethod visualize DiscretePoset
  [^DiscretePoset coll] (visualize (underlying-relation coll)))

(defmethod inverse-function DiscretePoset
  [^DiscretePoset poset] (->SetFunction (morphisms poset) (morphisms poset) identity))

; Products and coproducts of discrete posets
(defmethod product DiscretePoset
  [^DiscretePoset a, ^DiscretePoset b]

  (->DiscretePoset (product (objects a) (objects b))))

(defmethod coproduct DiscretePoset
  [^DiscretePoset a, ^DiscretePoset b]

  (->DiscretePoset (coproduct (objects a) (objects b))))

; Discrete posets are completely self-dual
(defmethod dual DiscretePoset
  [^DiscretePoset poset] poset)