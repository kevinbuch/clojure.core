(ns clojure.lang.persistent-set-helper
  (:refer-clojure :only [apply assoc cons defmacro defn defn- dissoc empty? every? fn flatten first keys let list list* loop map reduce repeat rest take + ->])
  (:require [clojure.lang.counted             :refer [count]]
            [clojure.lang.hash                :refer [hash]]
            [clojure.lang.lookup              :refer [contains?]]
            [clojure.lang.operators           :refer [=]]
            [clojure.lang.seqable             :refer [seq]]
            [clojure.lang.platform.comparison :refer [platform-equals-method]]
            [clojure.lang.platform.hash       :refer [platform-hash-method]]
            [clojure.lang.platform.object     :refer [expand-methods]]))

(defn make-pairs [xs]
  (flatten (map #(take 2 (repeat %)) xs)))

(defn- sets-reduce [accumulator-fn -map sets]
  (loop [remaining-sets sets
         new-map        -map]
    (if (empty? remaining-sets)
      new-map
      (recur (rest remaining-sets)
             (accumulator-fn new-map (seq (first remaining-sets)))))))

(defn set-difference [-map sets]
  (sets-reduce #(apply dissoc (cons %1 %2)) -map sets))

(defn set-union [-map sets]
  (sets-reduce #(apply assoc (cons %1 (make-pairs %2))) -map sets))

(defn set-intersection [-map sets]
  (reduce
    (fn [-acc-map k]
      (if (every? #(contains? % k) sets)
        -acc-map
        (dissoc -acc-map k)))
    -map (keys -map)))

(defn set-equals? [-map other-set]
  (if (= (clojure.core/count -map) (count other-set))
    (let [ks (keys -map)]
      (every? #(contains? other-set %) ks))
    false))

(defn set-hash [items-seq]
  (reduce #(+ %1 (hash %2)) 0 items-seq))

(defmacro set-equals?-init
  [this other-set]
  (list 'clojure.lang.persistent-set-helper/set-equals? '-map other-set))

(defmacro set-hash-init
  [this]
  (list 'clojure.lang.persistent-set-helper/set-hash (list 'clojure.lang.seqable/seq this)))

(def platform-set-methods
  (-> {}
    (platform-equals-method 'clojure.lang.persistent-set-helper/set-equals?-init)
    (platform-hash-method 'clojure.lang.persistent-set-helper/set-hash-init)
    expand-methods))

(defmacro defset [type gen-next]
  (list*
    'clojure.core/deftype type ['-map]

    'clojure.lang.icounted/ICounted
    (list '-count ['this]
      (list 'clojure.core/count (list 'clojure.core/keys '-map)))

    'clojure.lang.ilookup/ILookup
    (list '-lookup ['this 'x 'default]
      (list 'clojure.core/get '-map 'x 'default))

    (list '-includes? ['this 'x]
      (list 'clojure.core/contains? '-map 'x))

    'clojure.lang.ipersistent-set/IPersistentSet
    (list '-conj ['this 'xs]
      (list 'clojure.core/let ['next-map (list 'clojure.core/apply 'clojure.core/assoc '-map (list 'make-pairs 'xs))]
        (list gen-next 'next-map)))

    (list '-difference ['this 'sets]
      (list 'clojure.core/let ['next-map (list 'clojure.lang.persistent-set-helper/set-difference '-map 'sets)]
        (list gen-next 'next-map)))

    (list '-disj ['this 'xs]
      (list 'clojure.core/let ['next-map (list 'clojure.core/apply 'clojure.core/dissoc '-map 'xs)]
        (list gen-next 'next-map)))

    (list '-intersection ['this 'sets]
      (list 'clojure.core/let ['next-map (list 'clojure.lang.persistent-set-helper/set-intersection '-map 'sets)]
        (list gen-next 'next-map)))

    (list '-union ['this 'sets]
      (list 'clojure.core/let ['next-map (list 'clojure.lang.persistent-set-helper/set-union '-map 'sets)]
        (list gen-next 'next-map)))

    'clojure.lang.iseqable/ISeqable
    (list '-seq ['this] (list 'clojure.core/keys '-map))

    clojure.lang.persistent-set-helper/platform-set-methods))
