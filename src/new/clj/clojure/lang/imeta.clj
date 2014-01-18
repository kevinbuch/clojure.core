(ns clojure.lang.imeta
  (:refer-clojure :only [defprotocol]))

(defprotocol IMeta
  (-meta [this])
  (-with-meta [this new-meta])
  (-reset-meta! [this new-meta])
  (-alter-meta! [this f args]))
