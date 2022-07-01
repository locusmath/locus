(ns locus.geometry.commons.core
  (:import (org.apache.commons.math3.geometry.euclidean.threed Vector3D Euclidean3D)
           (org.apache.commons.math3.geometry.euclidean.twod Vector2D Euclidean2D)
           (org.apache.commons.math3.geometry.euclidean.oned Vector1D Euclidean1D)))

; Euclidean spaces in apache commons math
(def euclidean-1d
  (Euclidean1D/getInstance))

(def euclidean-2d
  (Euclidean2D/getInstance))

(def euclidean-3d
  (Euclidean3D/getInstance))

; Geometric vectors in the apache commons math system
(defn one-dimensional-vector
  [x]

  (Vector1D. x))

(defn two-dimensional-vector
  [x y]

  (Vector2D. x y))

(defn three-dimensional-vector
  [x y z]

  (Vector3D. x y z))

