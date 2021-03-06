(ns clojure.lang.apersistent-set
  (:refer-clojure :only [apply defmacro defn defn- fn flatten let list list* loop map ->])
  (:require [clojure.lang.deftype     :refer [expand-methods]]
            [clojure.lang.equivalence :refer [platform-equals-method]]
            [clojure.lang.hash        :refer [platform-hash-method]]
            [clojure.lang.protocols]
            [clojure.next             :refer :all]))

(defn make-pairs [xs]
  (loop [pairs xs
         acc []]
    (if (empty? pairs)
      acc
      (let [p (first pairs)]
        (recur (rest pairs) (clojure.core/conj acc p p))))))

(defn- sets-reduce [accumulator-fn -map sets]
  (loop [remaining-sets sets
         new-map        -map]
    (if (empty? remaining-sets)
      new-map
      (recur (rest remaining-sets)
             (accumulator-fn new-map (seq (first remaining-sets)))))))

(defn set-difference [-map sets]
  (sets-reduce #(reduce dissoc %1 %2) -map sets))

(defn set-union [-map sets]
  (sets-reduce #(apply assoc (clojure.core/cons %1 (make-pairs %2))) -map sets))

(defn set-intersection [-map sets]
  (loop [m -map
         ks (keys -map)]
    (if (empty? ks)
      m
      (let [k (first ks)]
        (if (every? #(contains? % k) sets)
          (recur m (rest ks))
          (recur (dissoc m k) (rest ks)))))))

(defn set-equals? [-map other-set]
  (if (= (count -map) (count other-set))
    (every? #(contains? other-set %) (keys -map))
    false))

(defn set-hash [items-seq]
  (reduce #(+ %1 (hash %2)) 0 items-seq))

(defmacro set-equals?-init
  [this other-set]
  (list 'clojure.lang.apersistent-set/set-equals? '-map other-set))

(defmacro set-hash-init
  [this]
  (list 'clojure.lang.apersistent-set/set-hash (list 'clojure.next/seq this)))

(def platform-set-methods
  (-> {}
    (platform-equals-method 'clojure.lang.apersistent-set/set-equals?-init)
    (platform-hash-method 'clojure.lang.apersistent-set/set-hash-init)
    expand-methods))

(defmacro defset [type gen-next]
  (list*
    'clojure.core/deftype type ['-map]

    'clojure.lang.protocols/ICounted
    (list '-count ['this]
      (list 'clojure.next/count '-map))

    'clojure.lang.protocols/ILookup
    (list '-lookup ['this 'x 'default]
      (list 'clojure.next/get '-map 'x 'default))

    'clojure.lang.protocols/IPersistentSet
    (list '-contains? ['this 'x]
      (list 'clojure.next/contains? '-map 'x))

    (list '-difference ['this 'sets]
      (list 'clojure.core/let ['next-map (list 'clojure.lang.apersistent-set/set-difference '-map 'sets)]
        (list gen-next 'next-map)))

    (list '-disj ['this 'x]
      (list 'clojure.core/let ['next-map (list 'clojure.next/dissoc '-map 'x)]
        (list gen-next 'next-map)))

    (list '-intersection ['this 'sets]
      (list 'clojure.core/let ['next-map (list 'clojure.lang.apersistent-set/set-intersection '-map 'sets)]
        (list gen-next 'next-map)))

    (list '-union ['this 'sets]
      (list 'clojure.core/let ['next-map (list 'clojure.lang.apersistent-set/set-union '-map 'sets)]
        (list gen-next 'next-map)))

    'clojure.lang.protocols/IPersistentCollection
    (list '-cons ['this 'x]
      (list 'clojure.core/let ['next-map (list 'clojure.next/assoc '-map 'x 'x)]
        (list gen-next 'next-map)))

    (list '-empty ['this]
      (list gen-next (list 'clojure.next/empty '-map)))

    'clojure.lang.protocols/ISeqable
    (list '-seq ['this]
      (list 'clojure.next/seq (list 'clojure.next/keys '-map)))

    clojure.lang.apersistent-set/platform-set-methods))
