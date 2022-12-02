(ns locus.quiver.binary.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]))

; A quiver is an element of a concrete copresheaf topos. Its elements are therefore sections,
; which means that they are members of the sets associated to the objects of the index
; category of the copresheaf. In the case of the topos of quivers, Quiv, there are two objects
; of the underlying index category so there are two types of sections: objects and
; morphisms. We deal with these two types of elements of quivers here and we provide an
; overloaded multimethod for constructing elements of quivers.
(deftype QuiverObject [quiver object]
  Element
  (parent [this]
    quiver)

  SectionElement
  (tag [this] 1)
  (member [this] object)

  Object
  (equals [this b]
    (and
      (instance? QuiverObject b)
      (= (.quiver this) (.-quiver ^QuiverObject b))
      (= (.object this) (.-object ^QuiverObject b))))

  IdentifiableInstance
  (unwrap [this]
    (list (tag this) (member this))))

(deftype QuiverMorphism [quiver morphism]
  Element
  (parent [this]
    quiver)

  SectionElement
  (tag [this] 0)
  (member [this] morphism)

  IdentifiableInstance
  (unwrap [this]
    (list (tag this) (member this)))

  Object
  (equals [this b]
    (and
      (instance? QuiverMorphism b)
      (= (.-quiver this) (.-quiver ^QuiverMorphism b))
      (= (.-morphism this) (.-morphism ^QuiverMorphism b))))

  AbstractMorphism
  (source-object [this]
    (QuiverObject. quiver (source-element quiver morphism)))
  (target-object [this]
    (QuiverObject. quiver (target-element quiver morphism))))

(derive QuiverObject :locus.base.logic.structure.protocols/element)
(derive QuiverMorphism :locus.base.logic.structure.protocols/element)

(defmethod wrap :locus.quiver.base.core.protocols/structured-quiver
  [quiv [i v]]

  (cond
    (= i 0) (QuiverMorphism. quiv v)
    (= i 1) (QuiverObject. quiv v)))

; Quiver objects and morphisms
(defn quiver-objects
  [quiver]

  (set
    (map
      (fn [obj]
        (QuiverObject. quiver obj))
      (objects quiver))))

(defn quiver-morphisms
  [quiver]

  (set
    (map
      (fn [morphism]
        (QuiverMorphism. quiver morphism))
      (morphisms quiver))))

; Ontology of quiver elements
(defn quiver-element?
  [elem]

  (or
    (= (type elem) QuiverObject)
    (= (type elem) QuiverMorphism)))

; Ontology of objects of quivers
(defn quiver-object?
  [x]

  (= (type x) QuiverObject))

(defn endotrivial-quiver-object?
  [x]

  (and
    (quiver-object? x)
    (zero? (quiver-hom-cardinality (.quiver x) (.object x) (.object x)))))

(defn minimal-quiver-object?
  [x]

  (and
    (quiver-object? x)
    (zero? (quiver-vertex-proper-in-degree (.quiver x) (.object x)))))

(defn maximal-quiver-object?
  [x]

  (and
    (quiver-object? x)
    (zero? (quiver-vertex-proper-out-degree (.quiver x) (.object x)))))

(defn isolated-quiver-object?
  [x]

  (and
    (quiver-object? x)
    (let [q (.quiver x)
          o (.object x)]
      (= (quiver-vertex-proper-out-degree q o)
         (quiver-vertex-proper-out-degree q o)
         0))))

(defn empty-quiver-object?
  [x]

  (and
    (quiver-object? x)
    (let [q (.quiver x)
          o (.object x)]
      (= (quiver-vertex-in-degree q o)
         (quiver-vertex-out-degree q o)
         0))))

; Ontology of quiver morphisms
(defn quiver-morphism?
  [morphism]

  (= (type morphism) QuiverMorphism))

(defn quiver-endomorphism?
  [morphism]

  (and
    (quiver-morphism? morphism)
    (= (source-object morphism) (target-object morphism))))
