(ns locus.set.quiver.structure.core.protocols
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; Ontology of nary quivers:
; Nary quivers are collections of parallel functions between distinct sets
(derive ::structured-nary-quiver ::structured-set)
(derive ::nary-quiver :locus.set.logic.structure.protocols/copresheaf)
(derive ::nary-quiver ::structured-nary-quiver)
(derive ::thin-nary-quiver ::nary-quiver)

; Nullary quivers
(derive ::structured-diset ::structured-nary-quiver)
(derive ::diset ::nary-quiver)
(derive ::diset ::structured-diset)

; Unary quivers
(derive :locus.set.logic.structure.protocols/structured-function ::structured-nary-quiver)
(derive :locus.set.logic.structure.protocols/set-function ::nary-quiver)

; Binary quivers
(derive ::structured-quiver ::structured-nary-quiver)
(derive ::quiver ::nary-quiver)
(derive ::quiver ::structured-quiver)
(derive ::thin-quiver ::quiver)
(derive ::ab-quiver ::thin-quiver)

; Ternary quivers
(derive ::structured-ternary-quiver ::structured-nary-quiver)
(derive ::ternary-quiver ::nary-quiver)
(derive ::ternary-quiver ::structured-ternary-quiver)
(derive ::thin-ternary-quiver ::ternary-quiver)
(derive ::at-quiver ::thin-ternary-quiver)

; Ontology of morphisms of nary quivers
; Every presheaf topos of nary quivers has both objects and morphisms as elements.
(derive ::morphism-of-structured-nary-quivers ::structured-function)
(derive ::morphism-of-nary-quivers :locus.set.logic.structure.protocols/morphism-of-copresheaves)
(derive ::morphism-of-nary-quivers ::morphism-of-structured-nary-quivers)

; Morphisms of nullary quivers
(derive ::structured-difunction ::morphism-of-structured-nary-quivers)
(derive ::difunction ::morphism-of-nary-quivers)
(derive ::difunction ::structured-difunction)

; Morphisms of unary quivers
(derive ::structured-set-square ::morphism-of-structured-nary-quivers)
(derive ::set-square ::morphism-of-nary-quivers)
(derive ::set-square ::structured-set-square)

; Morphisms of binary quivers
(derive ::morphism-of-structured-quivers ::morphism-of-structured-nary-quivers)
(derive ::morphism-of-quivers ::morphism-of-nary-quivers)
(derive ::morphism-of-quivers ::morphism-of-structured-quivers)

; Morphisms of ternary quivers
(derive ::morphism-of-structured-ternary-quivers ::morphism-of-structured-nary-quivers)
(derive ::morphism-of-ternary-quivers ::morphism-of-nary-quivers)
(derive ::morphism-of-ternary-quivers ::morphism-of-structured-ternary-quivers)
(derive ::morphism-of-at-quivers ::morphism-of-ternary-quivers)

; Nary quivers are all structured disets and their morphisms are structured difunctions. While
; the morphisms in an nary quiver can be accessed by first-set and the objects can be accessed
; by second-set we provide for morphisms and objects methods to making accessing them easier.
(defprotocol StructuredDiset
  "The topos of pairs of sets Sets^2 is one of the most basic and fundamental of topoi
  studied in elementary topos theory. Consequently, there are a number of more advanced
  structures that are constructed over Sets^2, which require forgetful functors to it.
  Small categories themselves are a case in point, where the two sets are simply the
  object set and the morphism set of the category."

  (first-set [this]
    "The first set of the mapping of an object to the topos Sets^2.")
  (second-set [this]
    "The second set of the mapping of an object to the topos Sets^2."))

(defprotocol StructuredDifunction
  "This is the morphism part of a functor from a category into the topos Sets^2. It
   it is simply defined by taking a morphism and producing the pair of functions
   that define a morphism in the topos Sets^2."

  (first-function [this]
    "The first function in the mapping of a morphism to the topos Sets^2.")
  (second-function [this]
    "The second function in the mapping of a morphism to the topos Sets^2."))

; Set functions
(extend-type SetFunction
  StructuredDiset
  (first-set [this] (inputs this))
  (second-set [this] (outputs this)))

; Section elements of copresheaves
; Let F : C -> Sets be a copresheaf. Then a section of F is a pair of an object X of C and a member
; of the set F(X). The sections of a copresheaf are the elements of their underlying set, in our
; interpretation which takes copresheaves to be members of concrete topoi.
(defprotocol SectionElement
  "A protocol for defining sections of a copresheaf, which are elements x in F(o) for
  some object o in the category C for a copreshef topos Sets^C."

  (tag [this]
    "The containing object of the category that produces this section.")
  (member [this]
    "The member of the set produced by the copresheaf over this object."))

; Multimethods for quiver theory
; Morphisms and objects can be defined in terms of the mapping to the topos Sets^2 but in
; this case it is far more convenient to have shorthands like morphisms and objects
; as opposed to having to use first set and second set in every case.
(defn morphisms
  [quiv] (first-set quiv))

(defn objects
  [quiv] (second-set quiv))

; The topos theoretic foundations of abstract algebra are based upon the idea of a generalized
; nary quiver, which is a pair of sets with n-different parallel morphisms between them.
; These can be used to produce a topos theoretic perspective of nary operations for use in
; topos theoretic universal algebra. Topos theoretic algebraic structures, including globular
; sets and categories, are constructed by chaining various nary quivers together.
(defmulti quiver-arity type)

(defmethod quiver-arity ::diset
  [diset] 0)

(defmethod quiver-arity :locus.set.logic.structure.protocols/set-function
  [func] 1)

(defmethod quiver-arity ::quiver
  [quiver] 2)

(defmethod quiver-arity ::ternary-quiver
  [ternary-quiver] 3)

; Let Q be a nary quiver in the topos Sets^{T_{2,n}}.  Then each morphism in Q is associated to an
; array of objects whose size is equal to the arity of the quiver. Corresponding to this, we provide
; an essential nth-component function that can be used to get the object at the nth component of
; a morphism in a nary quiver. In a binary quiver, the source object is the component at index one
; and the target object is the component at index two.
(defmulti nth-component (fn [quiver edge i] (type quiver)))

(defmethod nth-component ::diset
  [diset edge i]

  (throw (new IndexOutOfBoundsException)))

(defmethod nth-component :locus.set.logic.structure.protocols/set-function
  [func edge i]

  (func edge))

; A nary quiver is a copresheaf and if it is of arity n then it has n different non-identity
; morphisms, each of which can be defined by the nth component function. These functions
; allow us to treat nary quivers as copresheaves over an appropriate parallel arrows category.
(defn nth-component-function
  [quiver i]

  (->SetFunction
    (morphisms quiver)
    (objects quiver)
    (fn [morphism]
      (nth-component quiver morphism i))))

; Let Q be a nary-quiver. While we can use nth-component to get the individual objects associated
; to a morphism in such a quiver, we can use-morphism components to get a list of all objects
; associated to a morphism. In particular, for a binary quiver this produces an ordered pair
; and for a ternary quiver this produces an ordered triple.
(defn morphism-components
  [quiver morphism]

  (map
    (fn [i]
      (nth-component quiver morphism i))
    (range (quiver-arity quiver))))

; Get the dual of a structured quiver
(defmulti dual type)

; General mechanisms for copresheaves and other functors to be used in category theory
; Whenever we define a functor it should generally be applicable to either objects and
; morphisms and it should be constructed from a difunction which is a pair consisting
; of a morphism function and an object function that can be applied to these respective
; categorical elements.
(defn object-apply
  [functor obj]

  ((second-function functor) obj))

(defn morphism-apply
  [functor morphism]

  ((first-function functor) morphism))

; Default implementations of the get object and get morphism multimethods
(defmethod get-object :default
  [functor object]

  (object-apply functor object))

(defmethod get-morphism :default
  [functor morphism]

  (morphism-apply functor morphism))

; Numbers of objects and morphisms in a nary quiver
(defn quiver-size
  [quiv]

  (count (morphisms quiv)))

(defn quiver-order
  [quiv]

  (count (objects quiv)))

; Ontology of nary quivers
(defmulti nary-quiver? type)

(defmethod nary-quiver? :default
  [x] (isa? (type x) ::nary-quiver))

; Ontology of structured nary quivers
(defmulti structured-nary-quiver? type)

(defmethod structured-nary-quiver? :default
  [x] (isa? (type x) ::structured-nary-quiver))

; Ontology of structured nullary quivers
(defmulti structured-diset? type)

(defmethod structured-diset? :default
  [x] (isa? (type x) ::structured-diset))

; Ontology of structured binary quivers
(defmulti structured-quiver? type)

(defmethod structured-quiver? :default
  [x] (isa? (type x) ::structured-quiver))

; Ontology of morphisms of nary quivers
(defmulti morphism-of-nary-quivers? type)

(defmethod morphism-of-nary-quivers? :default
  [x] (isa? (type x) ::morphism-of-nary-quivers))

; Ontology of structured morphisms of nary quivers
(defmulti morphism-of-structured-nary-quivers? type)

(defmethod morphism-of-structured-nary-quivers? :default
  [x] (isa? (type x) ::morphism-of-structured-nary-quivers))

; Ontology of morphisms of structured nullary quivers
(defmulti structured-difunction? type)

(defmethod structured-difunction? :default
  [x] (isa? (type x) ::structured-difunction))

; Ontology of morphisms of structured quivers
(defmulti morphism-of-structured-quivers? type)

(defmethod morphism-of-structured-quivers? :default
  [x] (isa? (type x) ::morphism-of-structured-quivers))

; Generate copresheaf data that can be used for visualisation routines
; For example, this is useful to display diagrams of morphisms of functions
(defn generate-copresheaf-data
  [object-family morphism-triples]

  (list
    object-family
    (apply
      union
      (map
        (fn [[s t func]]
          (set
            (map
              (fn [input]
                (list
                  (list s input)
                  (list t (func input))))
              (inputs func))))
        morphism-triples))))

(defn relation-transition-map
  [rel i j]

  (loop [current-map {}
         current-in #{}
         current-out #{}
         current-rel (seq rel)]
    (if (empty? current-rel)
      (->SetFunction
        current-in
        current-out
        current-map)
      (let [current-element (first current-rel)
            a (nth current-element i)
            b (nth current-element j)]
        (recur
          (conj current-map [a b])
          (conj current-in a)
          (conj current-out b)
          (rest current-rel))))))

; The paths of a category include all elements of its composition domain
(defmulti paths type)

; Methods for locally ordered quivers and categories
(defmulti submorphism? (fn [a b] [(type a) (type b)]))

(defmulti meet-morphisms (fn [a b] [(type a) (type b)]))

(defmulti join-morphisms (fn [a b] [(type a) (type b)]))

; Display tables of semigroups, magmas, partial magmas, groups, categories, semicategories,
; groupoids, magmoids, or any other table like algebraic structure.
(defmulti display-table type)

(defn ^{:private true} display-table-by-parts*
  [potential-domain actual-domain vertices op]

  (let [n (count vertices)
        elems (vec (seq vertices))
        coll (into
               {}
               (map
                 (fn [[a b]]
                   (let [i (.indexOf elems a)
                         j (.indexOf elems b)
                         k (.indexOf elems (op (list a b)))]
                     [[i j] k]))
                 actual-domain))
        rel (set (keys coll))
        indices (range n)
        table (map
                (fn [i]
                  (map
                    (fn [j]
                      (if (contains? rel [i j])
                        (str (get coll [i j]))
                        (if (contains? potential-domain [(nth elems i) (nth elems j)])
                          "■"
                          "■")))
                    indices))
                indices)]
    (doseq [i table]
      (println (apply str (interpose " " i))))))

(defmethod display-table :locus.set.logic.structure.protocols/set-function
  [func]

  (let [coll (set (inputs func))]
    (display-table-by-parts* coll coll (set (outputs func)) func)))

