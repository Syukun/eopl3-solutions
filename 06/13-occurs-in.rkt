#lang eopl
(define occurs-in?
  (lambda (n s)
    (if (null? s)
        0
        (if (number? (car s))
            (if (equal? n (car s))
                1
                (occurs-in? n (cdr s)))
            (if (occurs-in? n (car s))
                1
                (occurs-in? n (cdr s)))))))

;; 写一个尾递归版本的 occurs-in?
(define occurs-in?-tail
  (lambda (n s)
    (occurs-in?/k n s (end-cont))))

(define end-cont
  (lambda ()
    (lambda (val)
      (begin
        (eopl:printf "end-cont return only one time!\n")
        val))))

(define occurs-in?/k
  (lambda (n s cont)
    (if (null? s)
        (cont 0)
        (if (number? (car s))
            (if (equal? n (car s))
                (cont 1)
                (occurs-in?/k n (cdr s) cont))
            (if (occurs-in? n (car s))
                (cont 1)
                (occurs-in? n (cdr s) cont))))))
                
