#lang eopl
(provide (all-defined-out))
;; 主要用来是实现队列

(define empty-queue
  (lambda () '()))

(define empty? null?)

;; 进队列
(define enqueue
  (lambda (q val)
    (append q (list val))))
;; 出队列
(define dequeue
  (lambda (q f)
    (f (car q) (cdr q))))
