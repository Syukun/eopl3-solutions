#lang eopl
(provide (all-defined-out))
;; print 
;; �Զ���ĸ�������,�����ӡ��Ϣ
(define (print arg1 arg2)
  (begin
    (newline)
    (newline)
    (display arg1)
    (display arg2)
    (newline)))