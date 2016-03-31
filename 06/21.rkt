#lang eopl
;; 修改式子cps-of-call-exp使得operands从左至右计算
;; operands本来就是从左至右运算的
;; 不过这道题没什么营养。

;; cps-of-call-exp : InpExp * Listof(InpExp) * SimpleExp -> TfExp
;; Page: 220
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons  rands rator)
                 (lambda (new-rands)
                   (cps-call-exp
                    (last new-rands)
                    (append (remove-last new-rands) (list k-exp)))))))

(define last
  (lambda (lst)
    (if (null? (cdr lst))
	(car lst)
	(last (cdr lst)))))

(define remove-last-iter
  (lambda (lst cur)
    (if (null? (cdr lst))
	cur
	(remove-last-iter (cdr lst)
			  (append cur (list (car lst)))))))

(define remove-last
  (lambda (lst)
    (remove-last-iter lst '())))
