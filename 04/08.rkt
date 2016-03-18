#lang eopl

;; Show exactly where in our implementation of the store these operations take linear time rather than constant time
;; setref!函数的运行花费了线性的时间，而不是常数时间。
;; Procedure like setref! takes linear time rather than constant time.
;; since it will traverse the list in store.