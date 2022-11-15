(ns locus.elementary.preorder.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.preorder.core.object :refer :all]))

; Let C,D be thin categories. Then a functor f : C -> D is entirely determined by its object
; part. It follows that we can save memory by defining a special class for that only
; handles functors of thin categories. In this file, we provide that class.
(deftype MonotoneMap [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction
      (morphisms source)
      (morphisms target)
      (fn [edge]
        (map func edge))))
  (second-function [this]
    (->SetFunction
      (objects source)
      (objects target)
      func))

  ; Functional aspects of monotone maps
  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Monotone maps constitute functors
(derive MonotoneMap :locus.elementary.copresheaf.core.protocols/monotone-map)

; Composition and identities of thin categories
(defmethod identity-morphism :locus.elementary.copresheaf.core.protocols/thin-category
  [obj] (MonotoneMap. obj obj identity))

(defmethod compose* MonotoneMap
  [a b]

  (MonotoneMap.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

; Convert various types of functors into monotone maps
(defmulti to-monotone-map type)

(defmethod to-monotone-map MonotoneMap
  [^MonotoneMap func] func)

; Discrete monotone maps of preorders can be formed from set functions
(defn discrete-monotone-map
  [func]

  (->MonotoneMap
    (discrete-preorder (inputs func))
    (discrete-preorder (outputs func))
    func))

; Preorder images and inverse images
(defn preorder-image
  [func preorder]

  (let [rel (underlying-relation preorder)]
    (->Preposet
      (outputs func)
      (set
        (for [[a b] rel]
          (list (func a) (func b)))))))

(defn preorder-inverse-image
  [func preorder]

  (let [rel (underlying-relation preorder)]
    (->Preposet
     (inputs func)
     (fn [[a b]]
       (boolean (rel (list (func a) (func b))))))))

(defmethod image
  [:locus.base.logic.structure.protocols/set-function
   :locus.elementary.copresheaf.core.protocols/thin-category]
  [func preorder]

  (preorder-image func preorder))

(defmethod inverse-image
  [:locus.base.logic.structure.protocols/set-function
   :locus.elementary.copresheaf.core.protocols/thin-category]
  [func preorder]

  (preorder-inverse-image func preorder))

; Quotient related monotone maps
(defn quotient-monotone-map
  [rel partition]

  (MonotoneMap.
    (relational-preposet rel)
    (relational-preposet (cl preorder? (relation-quotient rel partition)))
    (fn [x]
      (projection partition x))))

(defn inclusion-monotone-map
  [rel coll]

  (MonotoneMap.
    (relational-preposet (subrelation rel coll))
    (relational-preposet rel)
    identity))

; Specialized monotone maps related to images/preimages
(defn induced-direct-image-monotone-map
  [func]

  (->MonotoneMap
    (->PowerSet (inputs func))
    (->PowerSet (outputs func))
    (fn [coll]
      (set-image func coll))))

(defn induced-inverse-image-monotone-map
  [func]

  (->MonotoneMap
    (->PowerSet (outputs func))
    (->PowerSet (inputs func))
    (fn [coll]
      (set-inverse-image func coll))))
