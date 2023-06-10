(ns locus.algebra.category.core.contravariant-functor
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; A contravariant functor F: C -> D is a functor F: C^{op} -> D.
(deftype ContravariantFunctor [source target morphism-function object-function]
  AbstractMorphism
  (source-object [this] (dual source))
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

; Contravariant functors are still functors
(derive ContravariantFunctor :locus.set.copresheaf.structure.core.protocols/functor)

; Contravariant functors use the dual of their input category for a source index
(defmethod index ContravariantFunctor
  [functor] (source-object functor))

; Contravariant functors can be treated like ordinary functors with associated objects and morphisms
(defmethod get-object ContravariantFunctor
  [functor x]

  ((second-function functor) x))

(defmethod get-morphism ContravariantFunctor
  [functor x]

  ((first-function functor) x))

; We can convert between covariant and contravariant functors by dualizing their source objects
(defmethod to-functor ContravariantFunctor
  [functor]

  (->Functor
    (dual (source-object functor))
    (target-object functor)
    (first-function functor)
    (second-function functor)))

(defmulti to-contravariant-functor type)

(defmethod to-contravariant-functor :locus.set.copresheaf.structure.core.protocols/functor
  [functor]

  (->ContravariantFunctor
    (dual (source-object functor))
    (target-object functor)
    (first-function functor)
    (second-function functor)))

; Dualizing between covariant and contravariant functors
(defmethod dual :locus.set.copresheaf.structure.core.protocols/functor
  [functor] (to-contravariant-functor functor))

(defmethod dual ContravariantFunctor
  [functor] (to-functor functor))

; Ontology of contravariant functors
(defn contravariant-functor?
  [functor]

  (= (type functor) ContravariantFunctor))
