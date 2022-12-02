(ns locus.elementary.action.core.protocols
  (:require [locus.base.logic.core.set :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]))

; Let C be a category and Arrows(C) its set of morphisms. Then we say that the
; morphisms of C act on Arrows(C) by its self induced actions either to the left or
; to the right. This produces the self induced morphism action preorders of the category C.
; But this is an action by partial transformations instead of by total ones. It follows
; from this that in principle we need generalized effect systems dealing with either
; partial or total transformations in order to fully support category theory.

; A basic protocol for defining effect systems
(defprotocol EffectSystem
  "An MSet is an object in a topos of copresheaves over a monoid. Then this is naturally associated
  with an action on the unique underlying set of associated to the unique object of the monoid. We
  can generalize this with the idea of an effect system, which allows us to also consider partial
  actions induced by inverse semigroups of partial permutations."

  (actions [this]
    "The actions of this effect system which can be applied to the action domain.")
  (action-domain [this action]
    "The objects that the actions of this effect system can be applied to.")
  (apply-action [this action arg]
    "This applies an action to an object of the action domain."))

; Fundamental operations for instances of effect systems
(defmulti action-representatives (fn [a b c] (type a)))

(defmethod action-representatives :default
  [es a b]

  (set
    (filter
      (fn [action]
        (and
          ((action-domain es action) a)
          (= (apply-action es action a) b)))
      (actions es))))

(defn action-relation
  [es action]

  (set
    (map
      (fn [i]
        (list i (apply-action es action i)))
      (action-domain es action))))

; The action preorder is the essential part the functorial adjointness relation between action
; preorders and the preorder based restrictions of effect systems.
(defmulti action-preorder type)

(defmethod action-preorder :default
  [this]

  (cl
    preorder?
    (apply
      union
      (map
        (fn [i]
          (action-relation this i))
        (actions this)))))

(defn seqable-action-preorder
  [ms]

  (->SeqableRelation
    (underlying-set ms)
    (fn [[a b]]
      (not
        (empty?
          (action-representatives ms a b))))
    {}))

(defmulti action-equality type)

(defmethod action-equality :default
  [ms]

  (pn
    (fn [a b]
      (and
        (= (action-domain ms a)
           (action-domain ms b))
        (every?
          (fn [i]
            (= (apply-action ms a i)
               (apply-action ms b i)))
          (action-domain ms a))))
    (actions ms)))

(defn action-closed-set?
  [ms coll]

  (every?
    (fn [action]
      (every?
        (fn [elem]
          (contains? coll (apply-action ms action elem)))
        coll))
    (actions ms)))

(defn action-closed-sets
  [ms]

  (set
    (filter
      (fn [i]
        (action-closed-set? ms i))
      (underlying-set ms))))

; Action homomorphisms
(defmulti action-homomorphism type)