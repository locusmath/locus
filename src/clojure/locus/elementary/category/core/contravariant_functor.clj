(ns locus.elementary.category.core.contravariant-functor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.preorder.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]))

; A contravariant functor F: C -> D is a functor F: C^{op} -> D.
(deftype ContravariantFunctor [source target morphism-function object-function]
  AbstractMorphism
  (source-object [this] (dual source))
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

; Contravariant functors are still functors
(derive ContravariantFunctor :locus.elementary.copresheaf.core.protocols/functor)

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

(defmethod to-contravariant-functor :locus.elementary.copresheaf.core.protocols/functor
  [functor]

  (->ContravariantFunctor
    (dual (source-object functor))
    (target-object functor)
    (first-function functor)
    (second-function functor)))

; Dualizing between covariant and contravariant functors
(defmethod dual :locus.elementary.copresheaf.core.protocols/functor
  [functor] (to-contravariant-functor functor))

(defmethod dual ContravariantFunctor
  [functor] (to-functor functor))

; Ontology of contravariant functors
(defn contravariant-functor?
  [functor]

  (= (type functor) ContravariantFunctor))
