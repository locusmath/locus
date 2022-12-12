(ns locus.set.tree.structure.core.protocols
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; The successor quiver at any point in a hierarchical cell complex
(defmulti successor-quiver (fn [quiv cell-type] (type quiv)))

; Get the arity of a successor quiver
(defmulti successor-arity (fn [quiv cell-type] (type quiv)))

(defmethod successor-arity :default
  [quiv cell-type]

  (quiver-arity (successor-quiver quiv cell-type)))

; Get the nth component function in a successor quiver
(defmulti nth-successor-function (fn [quiv cell-type i] (type quiv)))

(defmethod nth-successor-function :default
  [quiv cell-type i]

  (let [succ (successor-quiver quiv cell-type)]
    (nth-component-function succ i)))

(defmulti cell-components (fn [quiv cell-type elem] (type quiv)))

(defmethod cell-components :default
  [quiv cell-type elem]

  (let [succ (successor-quiver quiv cell-type)]
    (morphism-components succ elem)))

(defmulti nth-cell-component (fn [quiv cell-type elem i] (type quiv)))

(defmethod nth-cell-component :default
  [quiv cell-type elem i]

  (let [succ (successor-quiver quiv cell-type)]
    (nth-component succ elem i)))

; Get the underlying relations or multirelations of a successor quiver
(defn successor-relation
  [quiv cell-type]

  (underlying-relation (successor-quiver quiv cell-type)))

(defn successor-multirelation
  [quiv cell-type]

  (underlying-multirelation (successor-quiver quiv cell-type)))