#lang eopl
;; Implement the store in constant time by representing it as a scheme vector.
;; What is lost by using this representation?
;; 这种表示方法，使得vector的扩展变得很慢
(define the-store 'uninitialized)
(define size 100)
(define index 0)

;; empty-store : () -> Sto
(define empty-store
  (lambda () (make-vector size)))

;; get-store : () -> Sto
(define get-store
  (lambda () the-store))

;; initialize-store! : () -> Unspecified
(define initialize-store!
  (lambda ()
    (set! the-store (make-vector size))))

;; reference? : SchemeVal -> Bool
(define reference?
  (lambda (v)
    (integer? v)))

;; newref : Expval -> Ref
(define newref
  (lambda (val)
    (begin
      (vector-set! the-store index val)
      (set! index (+ index 1))
      (- index 1))))

;; deref : Ref -> ExpVal
(define deref
  (lambda (ref)
    (vector-ref the-store ref)))

;; setref! : Ref * ExpVal -> Unspecified
(define setref!
  (lambda (ref val)
    (vector-set! the-store ref val)))

;; test code
(initialize-store!)
(newref 10)
(deref 0)
(setref! 0 20)
(deref 0)






