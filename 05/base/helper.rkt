#lang eopl
(provide (all-defined-out))
;; print 
(define (print arg1 arg2)
  (begin
    (newline)
    (display arg1)
    (display arg2)
    (newline)))
