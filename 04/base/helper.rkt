#lang eopl
(provide (all-defined-out))
;; print 
;; 自定义的辅助函数,输出打印信息
(define (print arg1 arg2)
  (begin
    (newline)
    (newline)
    (display arg1)
    (display arg2)
    (newline)))