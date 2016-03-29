#lang eopl
;; 这道题目其实非常简单
(define list-sum
  (lambda (loi)
    (list-sum/k loi 0)))
(define list-sum/k
  (lambda (loi acc)
    (if (null? loi)
        acc
        (list-sum/k (cdr loi) (+ acc (car loi))))))