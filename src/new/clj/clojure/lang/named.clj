(ns clojure.lang.named
  (:refer-clojure :only [defn])
  (:require [clojure.lang.inamed :refer [-name -namespace]]
            [clojure.lang.platform.named]))

(defn name [obj]
  (-name obj))

(defn namespace [obj]
  (-namespace obj))
