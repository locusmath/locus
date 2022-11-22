(ns locus.order.general.core.morphism
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
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]))

; Let C,D be thin categories. Then a functor f : C -> D is entirely determined by its object
; part. It follows that we can save memory by defining a special class for that only
; handles functors of thin categories. In this file, we provide that class.
(deftype MonotoneMap [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction (morphisms source) (morphisms target) (partial map func)))
  (second-function [this]
    (->SetFunction (objects source) (objects target) func))

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

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

; Get if a pair of preorders form a monotone map of a function
(defn monotone-pair?
  [func in-preorder out-preorder]

  (every?
    (fn [[a b]]
      (boolean (out-preorder (list (func a) (func b)))))
    in-preorder))

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

; The condensation of a preorder mapping it to a partial order forms a monotone map
(defn condensation-monotone-map
  [preposet]

  (let [rel (underlying-relation preposet)
        partition (strong-connectivity rel)]
    (->MonotoneMap
      preposet
      (->Preposet
        partition
        (relation-quotient rel partition))
      (fn [i]
        (projection partition i)))))

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

; Reflect principal ideals and filters in order to better understand residuated mappings, and their
; category which is equivalent to the category of adjoints of preorders
(defn reflect-principal-ideal
  [monotone-map x]

  (let [target-relation (underlying-relation (target-object monotone-map))]
    (set-inverse-image monotone-map (principal-ideal target-relation x))))

(defn reflect-principal-filter
  [monotone-map x]

  (let [target-relation (underlying-relation (target-object monotone-map))]
    (set-inverse-image monotone-map (principal-filter target-relation x))))

; The category Ord is a locally ordered category, in which two monotone maps are comparable
; to one another in the pointwise ordering.
(defn componentwise-stronger-monotone-map?
  [f g]

  (let [rel (underlying-relation (target-object f))]
    (every?
     (fn [i]
       (rel (list (f i) (g i))))
     (inputs f))))

; Stronger monotone maps are simply the ones that have larger preorders on their input and outputs
(defn stronger-monotone-map?
  [f g]

  (and
    (equal-functions? (underlying-function f) (underlying-function g))
    (superset?
      (list (underlying-relation (source-object f)) (underlying-relation (source-object g))))
    (superset?
      (list (underlying-relation (target-object f)) (underlying-relation (target-object g))))))

; Join or meet preorders of monotone maps with the same underlying-functions
(defn join-monotone-maps
  [& maps]

  (let [f (first maps)]
    (->MonotoneMap
     (apply join-preposets (map source-object maps))
     (apply join-preposets (map target-object maps))
     (fn [i]
       (f i)))))

(defn meet-monotone-maps
  [& maps]

  (let [f (first maps)]
    (->MonotoneMap
      (apply meet-preposets (map source-object maps))
      (apply meet-preposets (map target-object maps))
      (fn [i]
        (f i)))))

; Monotone maps are functors of thin categories
; Therefore, they can be added to our ontology of functors and semifunctors.
(defmulti monotone-map? type)

(defmethod monotone-map? :locus.elementary.copresheaf.core.protocols/monotone-map
  [monotone-map] true)

(defmulti monotone-transformation? type)

(defmethod monotone-transformation? MonotoneMap
  [monotone-map]

  (= (source-object monotone-map) (target-object monotone-map)))

(defmethod monotone-transformation? :default
  [monotone-map]

  (and
    (monotone-map? monotone-map)
    (= (source-object monotone-map) (target-object monotone-map))))

(defn increasing-monotone-map?
  [monotone-map]

  (and
    (monotone-transformation? monotone-map)
    (let [rel (underlying-relation (source-object monotone-map))]
      (every?
        (fn [i]
          (rel (list i (monotone-map i))))
        (inputs monotone-map)))))

(defn decreasing-monotone-map?
  [monotone-map]

  (and
    (monotone-transformation? monotone-map)
    (let [rel (underlying-relation (source-object monotone-map))]
      (every?
        (fn [i]
          (rel (list (monotone-map i) i)))
        (inputs monotone-map)))))

(defn ^{:private true} idempotent-element-of?
  [monotone-map x]

  (= (monotone-map (monotone-map x)) (monotone-map x)))

(defn idempotent-monotone-map?
  [monotone-map]

  (and
    (monotone-transformation? monotone-map)
    (every? (partial idempotent-element-of? monotone-map) (inputs monotone-map))))

(defn closure-operator?
  [monotone-map]

  (and
    (increasing-monotone-map? monotone-map)
    (every? (partial idempotent-element-of? monotone-map) (inputs monotone-map))))

(defn interior-operator?
  [monotone-map]

  (and
    (decreasing-monotone-map? monotone-map)
    (every? (partial idempotent-element-of? monotone-map) (inputs monotone-map))))

(defn identity-monotone-map?
  [monotone-map]

  (and
    (monotone-transformation? monotone-map)
    (every?
      (fn [i]
        (= (monotone-map i) i))
      monotone-map)))

; Componentwise orderings on monotone maps
(defn componentwise-minimal-monotone-map?
  [monotone-map]

  (and
    (monotone-map? monotone-map)
    (superset?
      (list
        (outputs monotone-map)
        (maximal-vertices (outputs monotone-map))))))

(defn componentwise-maximal-monotone-map?
  [monotone-map]

  (and
    (monotone-map? monotone-map)
    (superset?
      (list
        (inputs monotone-map)
        (minimal-vertices (outputs monotone-map))))))

; Residuated and coresiduated mappings are important to the theory of adjoints of preorders
(defmulti residuated-mapping? type)

(defmethod residuated-mapping? :default
  [mapping]

  (let [source-relation (underlying-relation (source-object mapping))]
    (and
     (monotone-map? mapping)
     (every?
       (fn [i]
         (let [reflected-set (reflect-principal-ideal mapping i)]
           (= (count (maximal-member-vertices source-relation reflected-set)) 1)))
       (outputs mapping)))))

(defmulti coresiduated-mapping? type)

(defmethod coresiduated-mapping? :default
  [mapping]

  (let [source-relation (underlying-relation (source-object mapping))]
    (and
     (monotone-map? mapping)
     (every?
       (fn [i]
         (let [reflected-set (reflect-principal-filter mapping i)]
           (= (count (minimal-member-vertices source-relation reflected-set)) 1)))
       (outputs mapping)))))

(defn biresiduated-mapping?
  [mapping]

  (and
    (residuated-mapping? mapping)
    (coresiduated-mapping? mapping)))

(defn residuated-transformation?
  [mapping]

  (and
    (residuated-mapping? mapping)
    (= (source-object mapping) (target-object mapping))))

(defn coresiduated-trasnformation?
  [mapping]

  (and
    (residuated-mapping? mapping)
    (= (source-object mapping) (target-object mapping))))

(defn biresiduated-transformation?
  [mapping]

  (and
    (residuated-mapping? mapping)
    (= (source-object mapping) (target-object mapping))))
