#lang eopl
;; translate
;; 工作量过大啊。要完成这个作业的话，要实现许多额外的feature

;(define removeall
;  (lambda (n lst)
;    (if (null? lst) lst
;        (if (list? (car lst))
;                   (cons (removeall n (car lst))
;                         (removeall n (cdr lst)))
;                   (if (equal? n (car lst))
;                       (removeall n (cdr lst))
;                       (cons (car lst)
;                             (removeall n (cdr lst))))))))

;; 这里直接用scheme代替算了。
;; write a tail form version
(define removeall-tail
  (lambda (n lst)
    (remove-iter n lst (end-cont))))

(define end-cont
  (lambda ()
    (lambda (val)
      (begin
        (eopl:printf "end-cont return only one time!\n")
        val))))


(define remove-iter
  (lambda (n lst cont)
    (if (null? lst)
        (cont lst)
        (if (list? (car lst))
            (remove-iter n (car lst)
                         (lambda (v1) (remove-iter n (cdr lst) (lambda (v2) (cont (cons v1 v2))))))
            (if (equal? n (car lst))
                (remove-iter n (cdr lst) cont)
                (remove-iter n (cdr lst) (lambda (v1) (cont (cons (car lst) v1)))))))))
