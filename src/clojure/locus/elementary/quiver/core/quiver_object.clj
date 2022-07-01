(ns locus.elementary.quiver.core.quiver-object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]))

; Let Q be a quiver and x an element of Ob(Q) then the quiver object associated
; with x is simply the ordered pair (Q,x) which contains both the underlying quiver
; of the object and the element of the quiver itself. This naturally generalises
; objects of categories and lattices.

(deftype QuiverObject [quiver object])

(defn quiver-objects
  [quiver]

  (set
    (map
      (fn [obj]
        (QuiverObject. quiver obj))
      (objects quiver))))

; Ontology of objects of quivers
(defn quiver-object?
  [x]

  (= (type x) QuiverObject))

(defn endomorphically-trivial-quiver-object?
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
