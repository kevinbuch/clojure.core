(ns clojure.next ; eventually, this will be clojure.core
  (:refer-clojure :only [*assert*
                         apply binding cond declare defmacro defmulti defmethod defn defn-
                         even? extend-type fn if-let let neg? pos? require satisfies?
                         doseq list list* load loop format pr-str into butlast when when-let])
  (:require [clojure.lang.equivalence]
            [clojure.lang.object     :as    platform-object]
            [clojure.lang.exceptions :refer [new-assertion-error new-argument-error new-exception new-out-of-bounds-exception]]
            [clojure.lang.random     :refer [rand-float]]
            [clojure.lang.protocols  :refer :all]))

(def ^:dynamic *clojure-version*
  {:major       1
   :minor       6
   :incremental 0})

(declare cons
         str
         seq first next)

(defn clojure-version []
  (str (:major *clojure-version*) "."
       (:minor *clojure-version*) "."
       (:incremental *clojure-version*)))

(defn instance? [c x]
  (platform-object/instance? c x))

(defn identical? [x y]
  (platform-object/identical? x y))

(defn class [x]
  (platform-object/class x))

(defn class? [c]
  (instance? platform-object/base-class c))

(defn nil? [n]
  (identical? n nil))

(defn true? [t]
  (identical? t true))

(defn false? [f]
  (identical? f false))

(defmacro and
  "Returns true if all expressions are logically truthy, false otherwise."
  ([] true)
  ([x] x)
  ([x & xs]
    `(let [and-expr# ~x]
       (if and-expr# (and ~@xs) and-expr#))))

(defmacro or
  "Returns true is any expression is logically truthy, false otherwise. If zero arguments are supplied then or will return nil."
  ([] nil)
  ([x] x)
  ([x & xs]
   `(if-let [or-expr# ~x]
      or-expr#
      (or ~@xs))))

(defn ratio? [x]
  (satisfies? IRatio x))

(defn integer? [x]
  (satisfies? IInteger x))

(defn float? [x]
  (satisfies? IFloat x))

(defn decimal? [x]
  (satisfies? IDecimal x))

(defn rational? [x]
  (or (integer? x) (ratio? x) (decimal? x)))

(defn associative? [x]
  (satisfies? IAssociative x))

(declare bigint)
(require ['clojure.lang.numbers :as 'platform-numbers
                                :refer ['numbers-equal? 'numbers-equivalent?
                                        'bshift-right 'bunsigned-shift-right 'bshift-left 'bnot 'band 'band-not 'bor 'bxor 'bclear 'bset 'bflip 'btest
                                        'increment 'incrementp 'decrement 'decrementp
                                        'add 'addp 'multiply 'multiplyp 'subtract 'subtractp 'divide 'quotient 'remainder
                                        'is-number? 'is-zero?
                                        '->short '->byte '->int '->long '->double '->float '->bigint '->biginteger '->bigdec
                                        'maximum 'lt 'lte]])

(defn number? [x]
  (is-number? x))

(defmacro when-not-nil [x y & body]
  ^:private
  `(let [x-nil?# (nil? ~x)
         y-nil?# (nil? ~y)]
     (cond
       (and x-nil?# y-nil?#)
       true
       (or x-nil?# y-nil?#)
       false
       :else
       ~@body)))

(defn- equal? [x y]
  (when-not-nil x y
    (if (and (number? x) (number? y))
      (numbers-equal? x y)
      (-equal? x y))))

(defn =
  "Equality. When provided with numbers performs numbers-equal?. Else, calls the -equal? method on the first argument."
  ([x] true)
  ([x y] (equal? x y))
  ([x y & more] (and (= x y) (apply = y more))))

(defn ==
  "Equivalence. Calls the platform numbers-equivalent? function with the arguments"
  ([x] true)
  ([x y] (numbers-equivalent? x y))
  ([x y & more] (and (== x y) (apply == y more))))

(defn not
  "Returns true if x is logical false, false otherwise."
  [x]
  (if x false true))

(defn boolean
  "Returns true if x is logical true, false otherwise."
  [x]
  (if x true false))

(defn not=
  "Same as (not (= obj1 obj2))."
  [& args]
  (not (apply = args)))

(defn not==
  "Same as (not (== obj1 obj2))."
  [& args]
  (not (apply == args)))

(defn byte [x]
  (->byte x))

(defn short [x]
  (->short x))

(defn int [x]
  (->int x))

(defn long [x]
  (->long x))

(defn double [x]
  (->double x))

(defn float [x]
  (->float x))

(defn bigint [x]
  (->bigint x))

(defn biginteger [x]
  (->biginteger x))

(defn bigdec [x]
  (->bigdec x))

(defn bit-shift-right [n shift]
  (bshift-right n shift))

(defn unsigned-bit-shift-right [n shift]
  (bunsigned-shift-right n shift))

(defn bit-shift-left [n shift]
  (bshift-left n shift))

(defn bit-not [x] (bnot x))

(defn bit-and
  ([n other] (band n other))
  ([n other & more] (clojure.core/reduce bit-and (bit-and n other) more)))

(defn bit-and-not
  ([n other] (band-not n other))
  ([n other & more] (clojure.core/reduce bit-and-not (bit-and-not n other) more)))

(defn bit-or
  ([n other] (bor n other))
  ([n other & more] (clojure.core/reduce bit-or (bit-or n other) more)))

(defn bit-xor
  ([n other] (bxor n other))
  ([n other & more] (clojure.core/reduce bit-xor (bit-xor n other) more)))

(defn bit-clear [x location]
  (bclear x location))

(defn bit-set [x location]
  (bset x location))

(defn bit-flip [x location]
  (bflip x location))

(defn bit-test [x location]
  (btest x location))

(defn +
  ([] 0)
  ([x] (add x 0))
  ([x y] (add x y))
  ([x y & more] (clojure.core/reduce + (+ x y) more)))

(defn +'
  ([] 0)
  ([x] (addp x 0))
  ([x y] (addp x y))
  ([x y & more] (clojure.core/reduce +' (+' x y) more)))

(defn -
  ([x] (subtract x))
  ([x y] (subtract x y))
  ([x y & more] (clojure.core/reduce - (- x y) more)))

(defn -'
  ([x] (subtractp x))
  ([x y] (subtractp x y))
  ([x y & more] (clojure.core/reduce -' (-' x y) more)))

(defn *
  ([] 1)
  ([x] (multiply x 1))
  ([x y] (multiply x y))
  ([x y & more] (clojure.core/reduce * (* x y) more)))

(defn *'
  ([] 1)
  ([x] (multiplyp x 1))
  ([x y] (multiplyp x y))
  ([x y & more] (clojure.core/reduce *' (*' x y) more)))

(defn /
  ([x] (/ 1 x))
  ([x y] (divide x y))
  ([x y & more] (clojure.core/reduce / (/ x y) more)))

(defn zero? [i]
  (is-zero? i))

(defn quot [n div]
  (quotient n div))

(defn rem [n div]
  (remainder n div))

(defn mod [n div]
  (let [modulus (rem n div)]
    (if (or (zero? modulus) (= (pos? n) (pos? div)))
      modulus
      (+ modulus div))))

(defn inc [i]
  (increment i))

(defn inc' [i]
  (incrementp i))

(defn dec [i]
  (decrement i))

(defn dec' [i]
  (decrementp i))

(defn max
  ([x] x)
  ([x y] (maximum x y))
  ([x y & more]
    (clojure.core/reduce max (max x y) more)))

(defn <
  ([a] true)
  ([a b] (lt a b))
  ([a b & more]
    (if (< a b)
      (if (next more)
        (recur b (first more) (next more))
        (< b (first more)))
      false)))

(defn <=
  ([a] true)
  ([a b] (lte a b))
  ([a b & more]
    (if (<= a b)
      (if (next more)
        (recur b (first more) (next more))
        (<= b (first more)))
      false)))

(defn >
  ([a] true)
  ([a b] (lt b a))
  ([a b & more]
    (if (> a b)
      (if (next more)
        (recur b (first more) (next more))
        (> b (first more)))
      false)))

(defn >=
  ([a] true)
  ([a b] (lte b a))
  ([a b & more]
    (if (>= a b)
      (if (next more)
        (recur b (first more) (next more))
        (>= b (first more)))
      false)))

(defn seq? [s]
  (satisfies? ISeq s))

(defn sequential? [s]
  (satisfies? ISequential s))

(defn empty [coll]
  (-empty coll))

(defn empty? [seqable]
  (not (seq seqable)))

(defn alter-meta! [m f & args]
  (-alter-meta! m f args))

(defn meta [m]
  (if (satisfies? IMeta m)
    (-meta m)))

(defn reset-meta! [m new-meta]
  (-reset-meta! m new-meta))

(defn with-meta [m new-meta]
  (-with-meta m new-meta))

(defn vary-meta [m f & args]
  (with-meta m (apply f (meta m) args)))

(defn first [s]
  (-first (seq s)))

(defn ffirst [s]
  (first (first s)))

(defn next [s]
  (-next (seq s)))

(defn nfirst [s]
  (next (first s)))

(defn nnext [s]
  (next (next s)))

(defn fnext [s]
  (first (next s)))

(defn rest [s]
  (-more (seq s)))

(defn last [s]
  (if (next s)
    (recur (next s))
    (first s)))

(defn second [s]
  (first (next s)))

(defn counted? [c]
  (satisfies? ICounted c))

(require ['clojure.lang.size :refer ['platform-count]])

(defn count [obj]
  (cond
    (counted? obj)
      (-count obj)
    (nil? obj)
      0
    (satisfies? IPersistentCollection obj)
      (loop [s (seq obj)
             cnt 0]
        (if s
          (if (counted? s)
            (recur (next s) (+ cnt (count s)))
            (recur (next s) (inc cnt)))
          cnt))
    :else
      (platform-count obj)))

(require ['clojure.lang.sequence :refer ['platform-seq 'make-iterator-seq]])

(defn seq [s]
  (cond
    (satisfies? ISeqable s)
      (-seq s)
    (nil? s)
      nil
    :else
      (platform-seq s)))

(defn iterator-seq [iter]
  (make-iterator-seq iter))

(defn identity [x] x)

(require ['clojure.lang.delay :refer ['new-delay '-force 'is-delay?]])

(defmacro delay [& body]
  (list 'clojure.lang.delay/new-delay (list* 'clojure.core/fn [] body)))

(defn delay? [d]
  (is-delay? d))

(defn deref
  ([obj] (-deref obj))
  ([obj timeout-ms timeout-val]
    (-blocking-deref obj timeout-ms timeout-val)))

(defn realized? [obj]
  (-is-realized? obj))

(defn force [obj]
  (-force obj))

(defn get
  ([coll k] (get coll k nil))
  ([coll k not-found]
    (if (satisfies? ILookup coll)
      (-lookup coll k not-found))))

(defn numerator [ratio]
  (-numerator ratio))

(defn denominator [ratio]
  (-denominator ratio))

(defn type [x]
  (or (get (meta x) :type) (class x)))

(defn name [named]
  (-name named))

(defn namespace [named]
  (-namespace named))

(defn peek [coll]
  (when coll
    (-peek coll)))

(defn pop [coll]
  (when coll
    (-pop coll)))

(defn rand
  ([] (rand-float))
  ([n] (* n (rand))))

(defn rand-int [n]
  (int (rand n)))

(require ['clojure.lang.aseq])
(require ['clojure.lang.seqable])

(require ['clojure.lang.cons :refer ['make-cons]])

(defn cons [elem seqable]
  (if (nil? seqable)
    (list elem)
    (if (satisfies? ISeq seqable)
      (make-cons elem seqable)
      (make-cons elem (seq seqable)))))

(defn first [s]
  (-first (seq s)))

(defn ffirst [s]
  (first (first s)))

(defn next [s]
  (-next (seq s)))

(defn nfirst [s]
  (next (first s)))

(defn nnext [s]
  (next (next s)))

(defn fnext [s]
  (first (next s)))

(defn rest [s]
  (-more (seq s)))

(defn last [s]
  (if (next s)
    (recur (next s))
    (first s)))

(defn second [s]
  (first (next s)))

(declare atom)
(declare reset!)
(require ['clojure.lang.lazy-seq :refer ['make-lazy-seq]])

(defmacro lazy-seq [& s-body]
  (list make-lazy-seq (list* 'clojure.core/fn [] s-body)))

(defn constantly [rval]
  (fn [& args] rval))

(defn take [n coll]
  (lazy-seq
    (when (pos? n)
      (when-let [s (seq coll)]
        (cons (first s) (take (dec n) (next s)))))))

(defn take-while [pred coll]
  (lazy-seq
    (when-let [s (seq coll)]
      (when (pred (first s))
        (cons (first s) (take-while pred (next s)))))))

(defn repeat
  ([x] (lazy-seq (cons x (repeat x))))
  ([n x] (take n (repeat x))))

(defn repeatedly
  ([f] (lazy-seq (cons (f) (repeatedly f))))
  ([n f] (take n (repeatedly f))))

(defn conj
  ([] [])
  ([coll] coll)
  ([coll x] (-cons coll x))
  ([coll x & xs]
   (if xs
     (recur (conj coll x) (first xs) (next xs))
     (conj coll x))))

(defn disj
  ([s] s)
  ([s x]
    (when s
      (-disj s x)))
  ([s x & xs]
    (when s
      (let [ret (-disj s x)]
        (if xs
          (recur ret (first xs) (next xs))
          ret)))))

(defn every? [pred s]
  (let [sq (seq s)]
    (cond
      (nil? s) true
      (pred (first sq)) (recur pred (next sq))
      :else false)))

(defn- nth-sequential
  ([coll n]
    (loop [s (seq coll)
           cnt 0]
      (if (nil? s)
        (throw (new-out-of-bounds-exception ""))
        (if (= cnt n)
          (first s)
          (recur (next s) (inc cnt))))))
  ([coll n not-found]
    (loop [s (seq coll)
           cnt 0]
      (if (nil? s)
        not-found
        (if (= cnt n)
          (first s)
          (recur (next s) (inc cnt)))))))

(defn nth
  ([coll n]
    (cond
      (satisfies? IIndexed coll) (-nth coll n)
      (satisfies? ISequential coll) (nth-sequential coll n)))
  ([coll n not-found]
    (cond
      (satisfies? IIndexed coll) (-nth coll n not-found)
      (satisfies? ISequential coll) (nth-sequential coll n not-found))))

(defn hash [obj]
  (-hash obj))

(defn key [entry]
  (-key entry))

(defn val [entry]
  (-val entry))

(declare contains?)
(require ['clojure.lang.persistent-map :refer ['new-key-seq 'new-val-seq]])

(defn keys [m]
  (new-key-seq (seq m)))

(defn vals [m]
  (new-val-seq (seq m)))

(defn assoc-seq [m kvs]
  (if kvs
    (let [n (next kvs)]
      (recur (-assoc m (first kvs) (first n)) (next n)))
    m))

(defn assoc
  ([m k v]
   (-assoc m k v))
  ([m k v & kvs]
   (assoc-seq (-assoc m k v) (seq kvs))))

(defn- dissoc-seq [m ks]
  (if ks
    (recur (-dissoc m (first ks)) (next ks))
    m))

(defn dissoc
  ([m] m)
  ([m k] (-dissoc m k))
  ([m k & ks]
   (dissoc-seq (-dissoc m k) (seq ks))))

(defn reduce
  ([f coll]
   (if-let [s (seq coll)]
     (reduce f (first s) (next s))
     (f)))
  ([f v coll]
    (loop [s coll
           acc v]
      (if (nil? s)
        acc
        (let [next-s (seq s)
              next-acc (f acc (first next-s))]
          (recur (next next-s) next-acc))))))

(defn transient [coll]
  (-as-transient coll))

(defn persistent! [coll]
  (-persistent coll))

(defn conj! [coll x]
  (-conj! coll x))

(defn assoc! [coll index x]
  (-assoc! coll index x))

(defn dissoc! [coll index]
  (-dissoc! coll index))

(defn pop! [coll]
  (-pop! coll))

(require ['clojure.lang.array :as 'arr])

(defn aset [arr i val]
  (arr/array-set! arr i val))

(defn aget [arr i]
  (arr/array-get arr i))

(defn alength [arr]
  (arr/array-length arr))

(defn aclone [arr]
  (arr/array-clone arr))

(defn acopy [src src-pos dest dest-pos length]
  (arr/array-copy src src-pos dest dest-pos length))

(defn make-array
  ([size] (make-array platform-object/base-object size))
  ([type size]
   (arr/make-array type size)))

(defn into-array
  ([seqable] (into-array platform-object/base-object seqable))
  ([type seqable]
   (let [s (seq seqable)
         size (count s)
         arr (make-array type size)]
     (loop [i 0 s s]
       (if (nil? s)
         arr
         (do
           (aset arr i (first s))
           (recur (inc i) (next s))))))))

(defn object-array [seq-or-size]
  (if (number? seq-or-size)
    (make-array platform-object/base-object seq-or-size)
    (into-array platform-object/base-object seq-or-size)))

(defn- number-array
  ([seq-or-size t]
    (if (number? seq-or-size)
      (make-array t seq-or-size)
      (into-array t seq-or-size)))
  ([size init-val-or-seq t]
    (if (instance? t init-val-or-seq)
      (let [ret (make-array t size)]
        (loop [remaining (dec size)]
          (do
            (aset ret remaining init-val-or-seq)
            (if (zero? remaining)
              ret
              (recur (dec remaining))))))
      (into-array t (take size init-val-or-seq)))))

(defn byte-array
  ([seq-or-size]
    (number-array seq-or-size platform-numbers/platform-byte))
  ([size init-val-or-seq]
    (number-array size init-val-or-seq platform-numbers/platform-byte)))

(defn short-array
  ([seq-or-size]
    (number-array seq-or-size platform-numbers/platform-short))
  ([size init-val-or-seq]
    (number-array size init-val-or-seq platform-numbers/platform-short)))

(defn int-array
  ([seq-or-size]
    (number-array seq-or-size platform-numbers/platform-int))
  ([size init-val-or-seq]
    (number-array size init-val-or-seq platform-numbers/platform-int)))

(defn long-array
  ([seq-or-size]
    (number-array seq-or-size platform-numbers/platform-long))
  ([size init-val-or-seq]
    (number-array size init-val-or-seq platform-numbers/platform-long)))

(defn float-array
  ([seq-or-size]
    (number-array seq-or-size platform-numbers/platform-float))
  ([size init-val-or-seq]
    (number-array size init-val-or-seq platform-numbers/platform-float)))

(defn double-array
  ([seq-or-size]
    (number-array seq-or-size platform-numbers/platform-double))
  ([size init-val-or-seq]
    (number-array size init-val-or-seq platform-numbers/platform-double)))

(defn vector? [v]
  (satisfies? IPersistentVector v))

(defn map? [m]
  (satisfies? IPersistentMap m))

(defn set? [s]
  (satisfies? IPersistentSet s))

(defn coll? [c]
  (satisfies? IPersistentCollection c))

(defn list? [l]
  (satisfies? IPersistentList l))

(defn string? [s]
  (instance? platform-object/platform-string s))

(require ['clojure.lang.persistent-vector :refer ['EMPTY-VECTOR 'is-chunked-seq?]])

(defn vector [& args]
  (let [arg-seq (seq args)
        empty-transient (-as-transient EMPTY-VECTOR)]
    (if arg-seq
      (loop [xs arg-seq v empty-transient]
        (if xs
          (recur (next xs) (-conj! v (first xs)))
          (-persistent v)))
      (-persistent empty-transient))))

(defn chunked-seq? [cs]
  (is-chunked-seq? cs))

(require ['clojure.lang.persistent-hash-map :refer ['new-hash-map 'EMPTY-HASH-MAP]])

(defn hash-map [& kvs]
  (let [kvs-seq (seq kvs)]
    (if kvs-seq
      (let [size (count kvs-seq)]
        (if (even? size)
          (loop [s kvs-seq m EMPTY-HASH-MAP]
            (if s
              (recur (next (next s)) (assoc m (first s) (first (next s))))
              m))
          (throw (new-argument-error
                   (format "PersistentHashMap can only be created with even number of arguments: %s arguments given"
                           size)))))
      EMPTY-HASH-MAP)))

(require ['clojure.lang.persistent-array-map :refer ['new-array-map]])

(defn array-map [& args]
  (let [sargs (seq args)
        size (count sargs)]
    (if (even? size)
      (new-array-map (into-array sargs) size (/ size 2) nil)
      (throw (new-argument-error
               (format "PersistentArrayMap can only be created with even number of arguments: %s arguments given"
                       size))))))

(require ['clojure.lang.apersistent-set :refer ['make-pairs]])
(require ['clojure.lang.persistent-hash-set :refer ['make-hash-set]])

(defn hash-set
  ([] (make-hash-set (hash-map)))
  ([& xs]
    (make-hash-set
      (apply hash-map (make-pairs xs)))))

(defn comparator [predicate]
  (fn [x y]
    (cond
      (predicate x y) -1
      (predicate y x) 1
      :else 0)))

(defn- compare-numbers [x y]
  (cond
    (< x y) -1
    (< y x) 1
    :else 0))

(defn compare [x y]
  (if (= x y)
    0
    (if (not (nil? x))
      (if (nil? y)
        1
        (if (number? x)
          (compare-numbers x y)
          (-compare-to x y)))
      -1)))

(require ['clojure.lang.persistent-sorted-map :refer ['make-sorted-map]])

(defn sorted-map-by [compare-fn & args]
  (let [comparable (comparator compare-fn)]
    (make-sorted-map comparable args)))

(defn sorted-map [& args]
  (make-sorted-map compare args))

(require ['clojure.lang.persistent-sorted-set :refer ['make-sorted-set]])

(defn sorted-set [& ks]
  (make-sorted-set
    (apply sorted-map (make-pairs ks))))

(defn sorted-set-by [compare-fn & ks]
  (make-sorted-set
    (apply sorted-map-by (clojure.core/cons compare-fn (make-pairs ks)))))

(defn contains? [coll k]
  (cond
    (nil? coll) false
    (satisfies? IAssociative coll) (-contains-key? coll k)
    (map? coll) (-contains-key? coll k)
    (set? coll) (-contains? coll k)
    :else (throw (new-argument-error (str "contains? not supported on type: " (type coll))))))

(defn get-validator [this]
  (-get-validator this))

(defn set-validator! [this validator-fn]
  (-set-validator! this validator-fn))

(defn add-watch [this k f]
  (-add-watch this k f))

(defn remove-watch [this k]
  (-remove-watch this k))

(defn compare-and-set! [atm old-val new-val]
  (-compare-and-set! atm old-val new-val))

(defn reset! [atm new-val]
  (-reset! atm new-val))

(defn swap!
  ([atm f] (-swap! atm f []))
  ([atm f x] (-swap! atm f [x]))
  ([atm f x y] (-swap! atm f [x y]))
  ([atm f x y & args] (-swap! atm f (into [x y] args))))

(require ['clojure.lang.agent :refer ['new-agent 'agent-get-error 'agent-restart 'agent-set-error-handler 'agent-get-error-handler
                                      'action-release-pending-sends
                                      'pooled-executor 'solo-executor]])
(require ['clojure.lang.thread :as 'threading])

(def ^:dynamic *agent* nil)

(defn- binding-conveyor-fn [f]
  (let [frame (clojure.lang.Var/cloneThreadBindingFrame)]
    (fn
      ([]
         (clojure.lang.Var/resetThreadBindingFrame frame)
         (f))
      ([x]
         (clojure.lang.Var/resetThreadBindingFrame frame)
         (f x))
      ([x y]
         (clojure.lang.Var/resetThreadBindingFrame frame)
         (f x y))
      ([x y z]
         (clojure.lang.Var/resetThreadBindingFrame frame)
         (f x y z))
      ([x y z & args]
         (clojure.lang.Var/resetThreadBindingFrame frame)
         (apply f x y z args)))))

(defn send-via [executor agnt f & args]
  (-dispatch agnt (binding [*agent* agnt] (binding-conveyor-fn f)) args executor))

(defn send [agnt f & args]
  (apply send-via pooled-executor agnt f args))

(defn send-off [agnt f & args]
  (apply send-via solo-executor agnt f args))

(defn release-pending-sends [] action-release-pending-sends)

(defn agent [state & args]
  (let [options (apply hash-map args)
        err-handler (get options :error-handler)]
    (new-agent state err-handler
               (get options :meta)
               (get options :validator)
               (get options :watches)
               (get options :error-mode
                 (if err-handler :continue :fail)))))

(defn agent-error [agnt]
  (agent-get-error agnt))

(defn agent-errors [agnt]
  (when-let [error (agent-error agnt)]
    (list error)))

(defn set-error-handler! [agnt error-fn]
  (agent-set-error-handler agnt error-fn))

(defn error-handler [agnt]
  (agent-get-error-handler agnt))

(defn restart-agent [agnt new-state & options]
  (let [opts (apply hash-map options)]
    (agent-restart agnt new-state opts)))

(defmacro io! [& body]
  (let [message (when (string? (first body)) (first body))
        body (if message (next body) body)]
    ; TODO stop relying on LockingTransaction
    `(if (clojure.lang.LockingTransaction/isRunning)
       (throw (new-argument-error ~(or message "I/O in transaction")))
       (do ~@body))))

(defn await [& agnts]
  (io! "await in transaction"
    (when *agent*
      (throw (new-exception "Can't wait in agent action")))
    (let [latch (threading/new-countdown-latch (clojure.core/count agnts))
          count-down (fn [agnt] (threading/latch-countdown latch) agnt)]
      (doseq [agnt agnts]
        (send agnt count-down))
      (threading/latch-await latch))))

(defn await-for [timeout-ms & agnts]
  (io! "await-for in transaction"
    (when *agent*
      (throw (new-exception "Can't wait in agent action")))
    (let [latch (threading/new-countdown-latch (clojure.core/count agnts))
          count-down (fn [agnt] (threading/latch-countdown latch) agnt)]
      (doseq [agnt agnts]
        (send agnt count-down))
      (threading/latch-await latch timeout-ms))))

(defn- setup-reference [reference options]
  (when-let [ref-meta (get options :meta)]
    (reset-meta! reference ref-meta))
  (when-let [validator (get options :validator)]
    (set-validator! reference validator))
    reference)

(require ['clojure.lang.atomic-ref :refer ['new-atomic-ref]])
(require ['clojure.lang.atom :refer ['new-atom]])

(defn atom
  ([state]
    (atom state :meta nil :validator nil))
  ([state & args]
    (let [config (apply array-map args)]
      (setup-reference
        (new-atom (new-atomic-ref state) nil nil (array-map))
        config))))

(defn memoize [f]
  (let [cache-atom (atom (hash-map))]
    (fn [& args]
      (let [cache (deref cache-atom)]
        (if (contains? cache args)
          (get cache args)
          (let [return-value (apply f args)]
            (swap! cache-atom assoc args return-value)
            return-value))))))

(require ['clojure.lang.ref :refer ['new-ref '-get-min-history '-set-min-history '-get-max-history '-set-max-history]])

(defn ref
  ([state]
   (ref state :max-history nil :min-history nil))
  ([state & args]
   (let [config (apply array-map args)]
     (setup-reference
       (new-ref (new-atomic-ref state)
                nil
                nil
                {}
                (get config :min-history)
                (get config :max-history))
       config))))

(defn ref-min-history
  ([ref]
   (-get-min-history ref))
  ([ref n]
   (-set-min-history ref n)))

(defn ref-max-history
  ([ref]
   (-get-max-history ref))
  ([ref n]
   (-set-max-history ref n)))

(require ['clojure.lang.stm :as 'stm])

(defmacro sync [flags & body]
  (stm/run-in-transaction (fn [] ~@body)))

(defmacro dosync [& body]
  `(sync nil ~@body))

(defmacro io! [& body])

(require ['clojure.lang.future :refer         ['new-future]])
(require ['clojure.lang.future-submission :as 'future-submission])

(defn future-call [f]
  (let [fun (binding-conveyor-fn f)]
    (new-future fun)))

(defmacro future [& body]
  `(future-call (^{:once true} fn* [] ~@body)))

(defn future? [f]
  (future-submission/is-future? f))

(defn future-cancel [f]
  (future-submission/cancel f true))

(defn future-cancelled? [f]
  (future-submission/is-cancelled? f))

(defn future-done? [f]
  (future-submission/is-done? f))

(require ['clojure.lang.hash :refer ['hash-combine]])
(require ['clojure.lang.show :refer ['build-string]])
(require ['clojure.lang.symbol :as 'sym])

(defn str
  ([] "")
  ([x]
   (if (nil? x) "" (-show x)))
  ([x & more]
   (build-string (clojure.core/cons x more))))

(defn symbol? [x]
  (sym/symbol? x))

(defn symbol
  ([name]
   (if (symbol? name)
     name
     (let [parts (clojure.string/split name #"/")]
       (if (= 1 (clojure.core/count parts))
         (symbol nil (clojure.core/first parts))
         (symbol (clojure.string/join "/" (butlast parts)) (clojure.core/last parts))))))
  ([ns name]
   (if (nil? name)
     (throw (Exception. "Can't create symbol with nil name")))
   (sym/new-symbol ns name (if ns (str ns "/" name) name)
               (hash (hash-combine (hash name) (hash ns))) nil)))

(require ['clojure.lang.atomic-counter :refer ['new-atomic-counter 'get-and-increment-atomic-counter]])

(def ^:private gensym-counter (new-atomic-counter 1))
(defn- next-gensym-value [] (get-and-increment-atomic-counter gensym-counter))

(defn gensym
  ([] (gensym "G__"))
  ([prefix] (symbol (str prefix (next-gensym-value)))))

(require ['clojure.lang.keyword :as 'kwd])

(defn keyword? [x]
  (kwd/keyword? x))

(defn keyword
  ([n]
   (let [sym (symbol n)]
     (keyword (namespace sym) (name sym))))
  ([ns name]
   (let [sym (symbol ns name)
         hash-code (hash (clojure.core/+ (hash sym) 0x9e3779b9))]
     (kwd/new-keyword ns name (str ":" sym) hash-code {} sym))))

(defmacro when-not [test & body]
  (list 'if test nil (clojure.core/cons 'do body)))

(defmacro assert
  ([assertion]
    (when *assert*
      `(when-not ~assertion
         (throw (new-assertion-error (str "Assert failed: " (pr-str '~assertion)))))))
  ([assertion message]
    (when *assert*
      `(when-not ~assertion
         (throw (new-assertion-error (str "Assert failed: " ~message "\n" (pr-str '~assertion))))))))

(defmacro while [test & body]
  `(loop []
     (when ~test
       `@body
       (recur))))

(def ^:dynamic *print-dup* false)
(def ^:dynamic *print-meta* false)
(def ^:dynamic *print-readably* true)
(def ^:dynamic *print-level* nil)
(def ^:dynamic *print-length* nil)
(def ^:dynamic *flush-on-newline* true)
(declare pr print-ctor)

(def char-escape-string
  (array-map
    \newline   "\\n"
    \tab       "\\t"
    \return    "\\r"
    \"         "\\\""
    \\         "\\\\"
    \formfeed  "\\f"
    \backspace "\\b"))

(def char-name-string
  (array-map
    \newline "newline"
    \tab "tab"
    \space "space"
    \backspace "backspace"
    \formfeed "formfeed"
    \return "return"))

(defmulti print-method (fn [obj writer]
                         (let [t (get (meta obj) (keyword "type"))]
                           (if (keyword? t) t (class obj)))))

(defmulti print-dup (fn [obj writer] (class obj)))

(require ['clojure.lang.input-output :refer ['default-out 'platform-out-str 'platform-append-space
                                             'platform-print-constructor
                                             'platform-newline 'platform-flush 'platform-write
                                             'print-map 'print-meta 'print-sequential]])
(def ^:dynamic *out* (default-out))

(defn newline []
  (platform-newline)
  nil)

(defn flush []
  (platform-flush)
  nil)

(defn print-ctor [obj print-args wrtr]
  (platform-print-constructor obj print-args wrtr))

(defn print-simple [obj wrtr]
  (print-meta obj wrtr)
  (platform-write wrtr (str obj)))

(defmethod print-method :default [obj wrtr]
  (print-simple obj wrtr))

(defmethod print-method nil [obj wrtr]
  (platform-write wrtr "nil"))

(defmethod print-method clojure.lang.keyword.Keyword [obj wrtr]
  (platform-write wrtr (str obj)))

(defmethod print-method clojure.lang.symbol.Symbol [obj wrtr]
  (print-simple obj wrtr))

(defmethod print-method clojure.lang.protocols.ISeq [obj wrtr]
  (print-meta obj wrtr)
  (print-sequential "(" print-method " " ")" obj wrtr))

(defmethod print-method clojure.lang.protocols.IPersistentMap [obj wrtr]
  (print-meta obj wrtr)
  (print-map obj print-method wrtr))

(defmethod print-method clojure.lang.protocols.IPersistentVector [obj wrtr]
  (print-meta obj wrtr)
  (print-sequential "[" print-method " " "]" obj wrtr))

(defmethod print-method clojure.lang.protocols.IPersistentSet [obj wrtr]
  (print-meta obj wrtr)
  (print-sequential "#{" print-method " " "}" obj wrtr))

(defmethod print-dup nil [obj wrtr]
  (print-method obj wrtr))

(defmethod print-dup clojure.lang.keyword.Keyword [obj wrtr]
  (print-method obj wrtr))

(defmethod print-dup clojure.lang.symbol.Symbol [obj wrtr]
  (print-method obj wrtr))

(defmethod print-dup clojure.lang.protocols.ISeq [obj wrtr]
  (print-method obj wrtr))

(defmethod print-dup clojure.lang.protocols.IPersistentList [obj wrtr]
  (print-method obj wrtr))

(defn pr-on [o w]
  (if *print-dup*
    (print-dup o w)
    (print-method o w))
  nil)

(defn pr
  ([] nil)
  ([obj]
    (pr-on obj *out*))
  ([x & more]
    (pr x)
    (platform-append-space *out*)
    (if-let [nmore (next more)]
      (recur (first more) nmore)
      (apply pr more))))

(defn prn [& more]
  (apply pr more)
  (platform-newline)
  (when *flush-on-newline*
    (platform-flush)))

(defn print [& more]
  (binding [*print-readably* nil]
    (apply pr more)))

(defn println [& more]
  (binding [*print-readably* nil]
    (apply prn more)))

(defmacro with-out-str [& body]
  `(let [o# (platform-out-str)]
    (binding [*out* o#]
      ~@body
      (str o#))))

(require ['clojure.lang.time :refer ['nano-time]])

(defmacro time [expr]
  `(let [start# (nano-time)
         ret# ~expr]
     (prn (str "Elapsed time: " (/ (double (- (nano-time) start#)) 1000000.0) " msecs"))
     ret#))

(require ['clojure.lang.persistent-list :refer ['EMPTY-LIST]])

(extend-type nil
  ISeqable
  (-seq [this] nil)
  ISeq
  (-first [this] nil)
  (-next [this] nil)
  (-more [this] EMPTY-LIST)
  IIndexed
  (-nth
    ([this n] nil)
    ([this n default] default)))

