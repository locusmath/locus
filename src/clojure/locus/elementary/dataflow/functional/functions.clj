(ns locus.elementary.dataflow.functional.functions
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.dataflow.functional.relations :refer :all]
            [locus.elementary.dataflow.functional.decomposition :refer :all]
            [locus.elementary.relational.relation.set-relation :refer :all]))

; We need this to function as the classifier for inputs and outputs of flow functions
(defn map-key-classifier
  [key-set]

  (fn [coll]
    (and
      (map? coll)
      (equal-universals? key-set (set (keys coll))))))

(defn create-composite-map
  [funcs coll]

  (into
    {}
    (map
      (fn [[k f]]
        [k (f coll)])
      funcs)))

; This is the higher abstraction layer over data dependencies modeled
; in the topos of functions, which uses the allegory of relations
(defprotocol RelationalDataflowModel
  (source-product-decomposition [this]
    "Get a product decomposition of the inputs set.")
  (target-product-decomposition [this]
    "Get a product decomposition of the outputs set.")
  (inverse-flow-relation [this]
    "Get a set relation between the two product decompositions."))

; Create a composite function from a flow model and a set of quotients.
(deftype CompositeMapFunction [in-keys out-keys rel components]
  AbstractMorphism
  (source-object [this] (map-keys-classifier in-keys))
  (target-object [this] (map-keys-classifier out-keys))

  ConcreteMorphism
  (inputs [this] (source-object this))
  (outputs [this] (target-object this))

  RelationalDataflowModel
  (source-product-decomposition [this] (map-keys-decomposition in-keys))
  (target-product-decomposition [this] (map-keys-decomposition out-keys))
  (inverse-flow-relation [this] rel)

  clojure.lang.IFn
  (invoke [this arg] (create-composite-map components arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Create a new composite map function system
(defn quotient-composite-map-function
  [func new-in-keys new-out-keys]

  (CompositeMapFunction.
    new-in-keys
    new-out-keys
    (restrict-set-relation (inverse-flow-relation func) new-out-keys new-in-keys)
    (select-keys (.components func) new-in-keys)))

; Here is an example of a composite map function
(def example-composite-map-function
  (CompositeMapFunction.
    #{:x :y :z}
    #{0 1}
    (->SetRelation
      #{0 1}
      #{:x :y :z}
      (fn [x]
        (case x
          0 #{:x :y}
          1 #{:y :z})))
    {0 (fn [coll]
         (+ (:x coll) (:y coll)))
     1 (fn [coll]
         (* (:y coll) (:z coll)))}))
