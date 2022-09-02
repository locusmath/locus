(ns locus.elementary.topoi.cube.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.elementary.function.inclusion.identity :refer :all]
            [locus.elementary.diamond.core.object :refer :all])
  (:import (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.function.core.object SetFunction)))

; Cubes are morphisms in the topos of diamonds
; At the same time, they themselves are also copresheaves in the topos of
; copresheaves over the cube shaped partial order. Diamond copresheaves play
; such a central role in mathematics, that we must have a special class
; defined for dealing with them.

(deftype Cube [source target f g h i]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target))d

; The morphic components of the cube morphism
(defn source-input-function
  [cube]

  (SetFunction.
    (source-input-set (source-object cube))
    (source-input-set (target-object cube))
    (.f cube)))

(defn source-output-function
  [cube]

  (SetFunction.
    (source-output-set (source-object cube))
    (source-output-set (target-object cube))
    (.g cube)))

(defn target-input-function
  [cube]

  (SetFunction.
    (target-input-set (source-object cube))
    (target-input-set (target-object cube))
    (.h cube)))

(defn target-output-function
  [cube]

  (SetFunction.
    (target-output-set (source-object cube))
    (target-output-set (target-object cube))
    (.i cube)))

; Constructors for cubes
(defmethod identity-morphism Diamond
  [diamond]

  (Cube. diamond diamond identity identity identity identity))

(defmethod compose* Cube
  [a b]

  (Cube.
    (source-object b)
    (target-object a)
    (comp (.f a) (.f b))
    (comp (.g a) (.g b))
    (comp (.h a) (.h b))
    (comp (.i a) (.i b))))

; Products and coproducts in the topos of cubes
(defmethod product Cube
  [& args]

  (->Cube
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map source-input-function args))
    (apply product (map source-output-function args))
    (apply product (map target-input-function args))
    (apply product (map target-output-function args)) ))

(defmethod coproduct Cube
  [& args]

  (->Cube
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map source-input-function args))
    (apply coproduct (map source-output-function args))
    (apply coproduct (map target-input-function args))
    (apply coproduct (map target-output-function args))))

; Ontology of cubes
(defn cube?
  [x]

  (= (type x) Cube))

