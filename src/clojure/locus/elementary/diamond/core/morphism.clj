(ns locus.elementary.diamond.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.base.effects.global.identity :refer :all]
            [locus.elementary.diamond.core.object :refer :all])
  (:import (locus.elementary.diamond.core.object Diamond)
           (locus.base.function.core.object SetFunction)))

; Cubes are morphisms in the topos of diamonds
; At the same time, they themselves are also copresheaves in the topos of
; copresheaves over the cube shaped partial order. Diamond copresheaves play
; such a central role in mathematics, that we must have a special class
; defined for dealing with them.

(deftype Cube [source target f g h i]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target))

; The morphic components of the cube morphism
(defn source-input-function
  [^Cube cube]

  (SetFunction.
    (source-input-set (source-object cube))
    (source-input-set (target-object cube))
    (.-f cube)))

(defn source-output-function
  [^Cube cube]

  (SetFunction.
    (source-output-set (source-object cube))
    (source-output-set (target-object cube))
    (.-g cube)))

(defn target-input-function
  [^Cube cube]

  (SetFunction.
    (target-input-set (source-object cube))
    (target-input-set (target-object cube))
    (.-h cube)))

(defn target-output-function
  [^Cube cube]

  (SetFunction.
    (target-output-set (source-object cube))
    (target-output-set (target-object cube))
    (.-i cube)))

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

; Subobject classifiers in the topos Sets^{[1,2,1]}
(def truth-diamond
  (let [in '#{((0 0) (1/3 1/3) (1/3 1/2) (1/2 1/3) (1/2 1/2) (1 1))}
        middle '#{0 1/2 1}
        out #{0 1}
        upper-function (mapfn {0 0, 1/2 1, 1 1})
        first-function (SetFunction.
                         in
                         middle
                         (fn [[a b]]
                           (cond
                             (= a 0) 0
                             (= a 1/3) 1/2
                             :else 1)))
        second-function (SetFunction.
                          in
                          middle
                          (fn [[a b]]
                            (cond
                              (= b 0) 0
                              (= b 1/3) 1/2
                              :else 1)))]
    (Diamond.
      first-function
      upper-function
      second-function
      upper-function)))

(defn subdiamond-truth
  [diamond new-source-inputs new-source-outputs new-target-inputs new-target-outputs]

  (->Cube
    diamond
    truth-diamond
    (fn [source-input]
      (if (contains? new-source-inputs source-input)
        (list 1 1)
        (list
          (cond
            (contains? new-source-outputs ((source-object diamond) source-input)) 1/2
            (contains? new-target-outputs ((common-composite-set-function diamond) source-input)) 1/3
            :else 0)
          (cond
            (contains? new-target-inputs ((first-function diamond) source-input)) 1/2
            (contains? new-target-outputs ((common-composite-set-function diamond) source-input)) 1/3
            :else 0))))
    (fn [source-output]
      (cond
        (contains? new-source-outputs source-output) 1
        (contains? new-target-outputs ((second-function diamond) source-output)) 1/2
        :else 0))
    (fn [target-input]
      (cond
        (contains? new-target-inputs target-input) 1
        (contains? new-target-outputs ((target-object diamond) target-input)) 1/2
        :else 0))
    (fn [target-output]
      (cond
        (contains? new-source-outputs target-output) 1
        :else 0))))

; Ontology of cubes
(defn cube?
  [x]

  (= (type x) Cube))

(defn endocube?
  [cube]

  (and
    (cube? cube)
    (= (source-object cube) (target-object cube))))

(defn identity-cube?
  [cube]

  (and
    (cube? cube)
    (identity-function? (source-input-function cube))
    (identity-function? (source-output-function cube))
    (identity-function? (target-input-function cube))
    (identity-function? (target-output-function cube))))