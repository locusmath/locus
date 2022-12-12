(ns locus.set.mapping.general.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]))

; Input and out elements of functions
(deftype InputElement [func in]
  Element
  (parent [this] func)

  IdentifiableInstance
  (unwrap [this]
    (list 0 in)))

(deftype OutputElement [func out]
  Element
  (parent [this] func)

  IdentifiableInstance
  (unwrap [this]
    (list 1 out)))

(derive InputElement :locus.set.logic.structure.protocols/function-element)
(derive OutputElement :locus.set.logic.structure.protocols/function-element)

(defmethod wrap :locus.set.logic.structure.protocols/set-function
  [func [i v]]

  (if (zero? i)
    (InputElement. func v)
    (OutputElement. func v)))

; Get the value of a part of a function
(defmulti get-function-member type)

(defmethod get-function-member InputElement
  [^InputElement elem]

  (.-in elem))

(defmethod get-function-member OutputElement
  [^OutputElement elem]

  (.-out elem))

; Methods on input elements
(defn application
  [^InputElement in]

  (OutputElement.
    (parent in)
    ((parent in) (get-function-member in))))

(defn equal-elements
  [^InputElement in]

  (let [func (parent in)]
    (set
      (map
        (fn [i]
          (InputElement. func i))
        (kernel-class-of func (get-function-member in))))))

(defn equal-elements-count
  [^InputElement in]

  (count (equal-elements in)))

; Methods on output elements
(defn output-fiber
  [^OutputElement out]

  (set
    (map
      (fn [i]
        (InputElement. (parent out) i))
      (fiber (parent out) (get-function-member out)))))

(defn output-fiber-cardinality
  [^OutputElement out]

  (count (output-fiber out)))

; Ontology of function elements
(defmulti function-element? type)

(defmethod function-element? :locus.set.logic.structure.protocols/function-element
  [x] true)

(defmethod function-element? :default
  [x] false)

(defn input?
  [x]

  (= (type x) InputElement))

(defn output?
  [x]

  (= (type x) OutputElement))

(defn missing-output?
  [x]

  (and
    (output? x)
    (zero? (output-fiber-cardinality x))))

(defn targeted-output?
  [x]

  (and
    (output? x)
    (not (zero? (output-fiber-cardinality x)))))

(defn injective-input?
  [x]

  (and
    (input? x)
    (= (equal-elements-count x) 1)))

(defn injective-output?
  [x]

  (and
    (output? x)
    (= (output-fiber-cardinality x) 1)))

(defn fixed-input?
  [x]

  (and
    (input? x)
    (let [func (parent x)
          elem (get-function-member x)]
      (= elem (func elem)))))

(defn moved-input?
  [x]

  (and
    (input? x)
    (not (fixed-input? x))))