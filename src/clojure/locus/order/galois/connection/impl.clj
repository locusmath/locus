(ns locus.order.galois.connection.impl
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.order.general.core.isomorphism :refer :all])
  (:import (locus.order.general.core.isomorphism PreorderIsomorphism)))

; A galois connection is a generalization of the relationship between images and inverse images
; in set theory. In particular, given a pair (S,T) we have that the pair forms a subfunction
; if T is closed under images or S is a subset of the inverse image. This is the most elementary
; example. The same principle applies elsewhere throughout mathematics, and it is generalized
; further by the definition of adjoints in category theory.

(deftype GaloisConnection [f g]
  AbstractMorphism
  (source-object [this] (source-object f))
  (target-object [this] (target-object f)))

; Convert various objects like order isomorphisms into galois connections
; Isomorphisms of partial orders are special cases of Galois connections in which the associated
; closure and dual closure operators of the Galois connection are both trivial.
(defmulti to-galois-connection type)

(defmethod to-galois-connection GaloisConnection
  [^GaloisConnection connection] connection)

(defmethod to-galois-connection PreorderIsomorphism
  [^PreorderIsomorphism preorder-isomorphism]

  (let [source (.-source preorder-isomorphism)
        target (.-target preorder-isomorphism)
        forwards (.-forwards preorder-isomorphism)
        backwards (.-backwards preorder-isomorphism)]
    (->GaloisConnection
      (->MonotoneMap source target forwards)
      (->MonotoneMap target source backwards))))

; The lower adjoint and right adjoint of a Galois connection are defined by overloaded
; multimethods that can also be applicable to adjoint functors of categories. The lower adjoint
; of a monotone Galois connection is a residuated mapping while the upper adjoint is a
; coresiduated mapping. Both residuated mappings and coresiduated mappings form their own
; categories which can be used to reconstruct the category of galois connections.
(defmulti lower-adjoint type)

(defmethod lower-adjoint GaloisConnection
  [^GaloisConnection connection]

  (.-f connection))

(defmulti upper-adjoint type)

(defmethod upper-adjoint GaloisConnection
  [^GaloisConnection connection]

  (.-g connection))

; The closed pairs of a Galois connection are fundamental objects of study
(defn closed-pair?
  [connection a b]

  (let [target-relation (underlying-relation (target-object connection))
        f (lower-adjoint connection)]
    (target-relation (list (f a) b))))

(defn closed-pairs
  [connection]

  (let [f (lower-adjoint connection)
        source (source-object connection)
        target (target-object connection)
        target-relation (underlying-relation target)]
    (set
      (mapcat
        (fn [a]
          (map
            (fn [i]
              (list a i))
            (principal-filter target-relation (f a))))
        (objects source)))))

; Get the closure and interior operators of a Galois connection
(defn associated-closure-operator
  [connection]

  (compose (upper-adjoint connection) (lower-adjoint connection)))

(defn associated-kernel-operator
  [connection]

  (compose (lower-adjoint connection) (upper-adjoint connection)))

; Every Galois connection has a set of fixed points that it maps between
(defn input-fixed-points
  [connection]

  (let [f (lower-adjoint connection)
        g (upper-adjoint connection)]
    (set
      (filter
        (fn [obj]
          (= obj (g (f obj))))
        (objects (source-object connection))))))

(defn output-fixed-points
  [connection]

  (let [f (lower-adjoint connection)
        g (upper-adjoint connection)]
    (set
      (filter
        (fn [obj]
          (= obj (f (g obj))))
        (objects (target-object connection))))))

; Galois connections are deemed to be composable mappings between preorders, so that they
; themselves form a category. They are also special types of adjoints.
(defmethod compose* GaloisConnection
  [^GaloisConnection a, ^GaloisConnection b]

  (->GaloisConnection
    (compose (lower-adjoint a) (lower-adjoint b))
    (compose (upper-adjoint b) (upper-adjoint a))))

; Monotone Galois connections are like presheaves of preorders. They are therefore an important
; part of our ontology emerging from our study of presheaves and preorders.
(defn monotone-galois-connection?
  [func]

  (= (type func) GaloisConnection))