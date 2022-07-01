(ns locus.linear.semimodule.utils
  (:require [locus.elementary.logic.base.core :refer :all]))

; The make shift global hierarchy of linear algebraic data types
; With this generic methods can be defined that are applicable to both
; modules and semimodules.
(derive ::module ::semimodule)
(derive ::vector-space ::module)

; Endomorphism algebras
; A semimodule is associated to an endomorphism semiring, and a module
; is associated to an endomorphism ring
(defmulti endomorphism-algebra type)

; Ontology of semimodules
(defmulti semimodule? type)

(defmethod semimodule? ::semimodule
  [semimodule] true)

(defmethod semimodule? :default
  [semimodule] false)

; Ontology of modules
(defmulti module? type)

(defmethod module? ::module
  [module] true)

(defmethod module? :default
  [module] false)