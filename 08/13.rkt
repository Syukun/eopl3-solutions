#lang eopl

;; write a module that implement arithmetic using a representation in which the integer k is represented as 5 * k + 3
module ints
 interface
  [ opaque t
    zero : t
    succ : (t -> t)
    pred : (t -> t)
    is-zero : (t -> bool) ]
  body
  [ type t = int
    zero = 0
    succ = proc (x : t) -(-(x, -5), -8)
    pred = proc (x : t) -(-(x, -5), 2)
    is-zero? = proc (x : t) zero? (-(x, 3)) ]

;; 好吧，这个表示应该没有什么错误
;; 这里的3代表0，所以判断是否为0的话，直接判断x-3是否为0即可
;; 这里的k用5*k+3表示，k-1表示为5*(k-1)+3=5*k-2
;; k+1表示5*(k+1)+3值为5*k+8
