(ns clojure.lang.keyword-test
  (:refer-clojure :only [let + defmacro nil?])
  (:require [clojure.test                 :refer :all]
            [clojure.lang.assertions      :refer [is-equal is-less-than is-greater-than]]
            [clojure.lang.hash            :refer [hash]]
            [clojure.lang.keyword         :refer [keyword keyword?]]
            [clojure.lang.meta            :refer [meta with-meta]]
            [clojure.lang.named           :refer [name namespace]]
            [clojure.lang.operators       :refer [not not= not== = ==]]
            [clojure.lang.platform.object :refer [identical?]]
            [clojure.lang.show            :refer [str]]
            [clojure.lang.symbol          :refer [symbol]]))

(deftest keyword-test
  (testing "creates a keyword from a name"
    (let [kwd (keyword "kwd")]
      (is (= "kwd" (name kwd)))))

  (testing "has no namespace by default"
    (let [kwd (keyword "kwd")]
      (is (= nil (namespace kwd)))))

  (testing "equivalent keywords has equivalent hash codes"
    (is (= (hash (keyword "kwd"))
           (hash (keyword "kwd"))))
    (is (= (hash (keyword "ns" "kwd"))
           (hash (keyword "ns" "kwd")))))

  (testing "keywords that are not equal have different hash codes"
    (is (not= (hash (keyword "kwd"))
              (hash (keyword "kwd1"))))
    (is (not= (hash (keyword "ns" "kwd"))
              (hash (keyword "ns" "kwd1"))))
    (is (not= (hash (keyword "ns" "kwd"))
              (hash (keyword "ns1" "kwd")))))

  (testing "creates a keyword with a namespace"
    (is (= "the-ns" (namespace (keyword "the-ns" "kwd")))))

  (testing "creates a keyword with a namespace-qualified name"
    (let [kwd (keyword "the-ns/kwd")]
      (is (= "kwd" (name kwd)))
      (is (= "the-ns" (namespace kwd)))))

  (testing "creates a keyword with a namespace-qualified name that has many slashes"
    (let [kwd (keyword "the-ns/kwd/kw2")]
      (is (= "kwd/kw2" (name kwd)))
      (is (= "the-ns" (namespace kwd)))))

  (testing "returns the string representation of the keyword"
    (let [kwd1 (keyword "kwd1")
          kwd2 (keyword "the-ns" "kwd2")]
      (is (= ":kwd1" (str kwd1)))
      (is (= ":the-ns/kwd2" (str kwd2))))))

(deftest keyword?-test
  (testing "returns true if the given object is a keyword"
    (is (= true (keyword? (keyword "kwd")))))

  (testing "returns false if the given object is not a keyword"
    (is (= false (keyword? 1)))
    (is (= false (keyword? nil)))))

(deftest compare-test
  (testing "equal if ns and name are equal"
    (let [lhs (keyword "the-ns" "kwd")
          rhs (keyword "the-ns" "kwd")]
      (is-equal lhs rhs)))

  (testing "equal if only the name is equal"
    (let [lhs (keyword "kwd")
          rhs (keyword "kwd")]
      (is-equal lhs rhs)))

  (testing "not equal if the names are not equal"
    (is (not= (keyword "kwd1")
              (keyword "kwd2"))))

  (testing "not equal if the names are equal but the namespaces are not"
    (is (not= (keyword "ns1" "kwd")
              (keyword "ns2" "kwd"))))

  (testing "not equal if the namespaces are equal but the names are not"
    (is (not= (keyword "ns" "kwd1")
              (keyword "ns" "kwd2"))))

  (testing "not equal if either is nil"
    (is (not= nil (keyword "kwd")))
    (is (not= (keyword "kwd") nil)))

  (testing "returns 0 if the keywords are equal"
    (let [lhs (keyword "kwd")
          rhs (keyword "kwd")]
      (is-equal lhs rhs)))

  (testing "less than if lhs ns is nil and rhs ns is not nil"
    (let [lhs (keyword "kwd")
          rhs (keyword "the-ns" "kwd")]
      (is-less-than lhs rhs)))

  (testing "less than if lhs is nil"
    (let [lhs nil
          rhs (keyword "kwd")]
      (is-less-than lhs rhs)))

  (testing "greater than if lhs ns is not nil and rhs ns is nil"
    (let [lhs (keyword "the-ns1" "kwd")
          rhs (keyword "kwd")]
      (is-greater-than lhs rhs)))

  (testing "greater than if rhs is nil"
    (let [lhs (keyword "kwd")
          rhs nil]
      (is-greater-than lhs rhs)))

  (testing "less than if lhs ns is less than rhs ns"
    (let [lhs (keyword "a" "kwd")
          rhs (keyword "b" "kwd")]
      (is-less-than lhs rhs)))

  (testing "greater than if not equal and if lhs ns is greater than rhs ns"
    (let [lhs (keyword "b" "kwd")
          rhs (keyword "a" "kwd")]
      (is-greater-than lhs rhs)))

  (testing "less than if nses equal and if lhs name is less than rhs name"
    (let [lhs (keyword "ns" "a")
          rhs (keyword "ns" "b")]
      (is-less-than lhs rhs)))

  (testing "greater than if nses equal and if lhs name is greater than rhs name"
    (let [lhs (keyword "ns" "b")
          rhs (keyword "ns" "a")]
      (is-greater-than lhs rhs))))

(deftest ^:new keyword-equiv
  (testing "not equal unless other is also a keyword"
    (is (not= (keyword "kwd") (symbol "kwd")))
    (is (not== (keyword "kwd") (symbol "kwd")))))
