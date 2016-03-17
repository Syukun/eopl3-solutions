#lang eopl
(require "parse.rkt")
(require "helper.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   translator
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;; lexical address calculator ;;;;;;;;;;;;;;;;

;; translation-of-program : Program -> Nameless-program
;; Page: 96
(define translation-of-program
  (lambda (pgm)
    (cases program pgm
	   (a-program (exp1)
		      (a-program                    
		       (translation-of exp1 (init-senv)))))))

;; translation-of : Exp * Senv -> Nameless-exp
;; Page 97
(define translation-of
  (lambda (exp senv)
    (cases expression exp
      (const-exp (num) (const-exp num))
      (diff-exp (exp1 exp2)
                (begin
                  (print "translation-of.diff-exp : exp1 --> " exp1)
                  (print "translation-of.diff-exp : exp2 --> " exp2)
                  (print "translation-of.diff-exp : senv --> " senv)
                  (let [(res (diff-exp (translation-of exp1 senv) (translation-of exp2 senv)))]
                    (print "translation-of.diff-exp : res --> " res)
                    res
                  )))
                  
      (if-exp (exp1 exp2 exp3)
              (begin
                (print "translation-of.if-exp : exp1 --> " exp1)
                (print "translation-of.if-exp : exp2 --> " exp2)
                (print "translation-of.if-exp : exp3 --> " exp3)
                (print "translation-of.if-exp : senv --> " senv)
              (if-exp
               (translation-of exp1 senv)
               (translation-of exp2 senv)
               (translation-of exp3 senv))))  
      (zero?-exp (exp1)
                 (zero?-exp
                  (translation-of exp1 senv)))
      (cons-exp (first rest)
                (begin
                  (print "translation-of.cons-exp : first --> " first)
                  (print "translation-of.cons-exp : rest --> " rest)
                  (cons-exp
                   (translation-of first senv)
                   (translation-of rest senv))))
      (emptylist-exp ()
                     (begin
                       ;(print "translation-of.emptylist-exp : hi" )
                       (emptylist-exp)))
      (var-exp (var)
               (begin 
                 (print "translation-of.var-exp : var --> " var)
                 (nameless-var-exp
                  (apply-senv senv var))))
                ;; apply-senv是非常重要的一个表达式,表示从senv中查找var变量的位置的序号
      (let-exp (var exp1 body) ;; var 代表的是变量名
               (begin
                 (print "translation-of.let-exp : var --> " var)
                 (print "translation-of.let-exp : exp1 --> " exp1)
                 (print "translation-of.let-exp : body --> " body)
                 (let ((proc (translation-of exp1 senv))
                       (tb (translation-of body
                                           (extend-senv var senv))))
                   (print "translation-of.let-exp : proc --> " proc)
                   (print "translation-of.let-exp : tb --> " tb)
                   (nameless-let-exp
                    proc  ;;翻译exp1表达式          
                    tb)))) ;; 在翻译body表达式的时候添加了var这个变量名
      (letrec-exp (p-name p-arg p-body body)
                  (begin
                    (print "translation-of.letrec-exp : p-name --> " p-name)
                    (print "translation-of.letrec-exp : p-arg --> " p-arg)
                    (print "translation-of.letrec-exp : p-body --> " p-body)
                    (print "translation-of.letrec-exp : body --> " body)
                    (nameless-letrec-exp
                     (nameless-proc-exp
                      (translation-of p-body (extend-senv p-arg senv)))
                     (translation-of body (extend-senv p-name senv)))))
      (proc-exp (vars body)
                (begin
                  (print "translation-of.proc-exp : vars --> " vars)
                  (print "translation-of.proc-exp : body --> " body)
                  (nameless-proc-exp
                   (translation-of body
                                   (extend-senv* vars senv)))))
      (call-exp (rator rand)
                (begin
                  (print "translation-of.call-exp : rator --> " rator)
                  (print "translation-of.call-exp : rand --> " rand)
                  (call-exp
                   (translation-of rator senv)
                   rand)))
      
      (unpack-exp (alist vlist body)
                  (begin
                    (print "translation-of.unpack-exp : alist --> " alist)
                    (print "translation-of.unpack-exp : vlist --> " vlist)
                    (print "translation-of.unpack-exp : body --> " body))
                  (nameless-unpack-exp
                   (translation-of vlist senv)
                   (translation-of body (extend-senv-list alist senv)))
                  )
                    
      (cond-exp (conditions results)
                (let [(translated-cond-exp
                       (cond-exp
                        (map (lambda (x) (translation-of x senv)) conditions)
                        (map (lambda (x) (translation-of x senv)) results)))]
                  (begin
                    (print "translation-of.cond-exp : translated-cond-exp --> " translated-cond-exp)
                    translated-cond-exp))
                )
      
      (else (report-invalid-source-expression exp))
      )))


(define (extend-senv* varlist senv)
  (if (null? varlist) senv
      (extend-senv* (cdr varlist) (extend-senv (car varlist) senv))))

(define (extend-senv-list alist senv)
  (if (null? alist) senv
      (extend-senv-list (cdr alist) (extend-senv (car alist) senv))))

(define report-invalid-source-expression
  (lambda (exp)
    (eopl:error 'value-of 
		"Illegal expression in source code: ~s" exp)))


;;;;;;;;;;;;;;;; static environments ;;;;;;;;;;;;;;;;
  
;;; Senv = Listof(Sym)
;;; Lexaddr = N

;; empty-senv : () -> Senv
;; Page: 95
(define empty-senv
  (lambda ()
    '()))

;; extend-senv : Var * Senv -> Senv
;; Page: 95
(define extend-senv
  (lambda (var senv)
    (cons var senv)))
  
;; apply-senv : Senv * Var -> Lexaddr
;; Page: 95
(define apply-senv
  (lambda (senv var)
    (cond
     ((null? senv) (report-unbound-var var))
     ((eqv? var (car senv))
      0)
     (else
      (+ 1 (apply-senv (cdr senv) var))))))

(define report-unbound-var
  (lambda (var)
    (eopl:error 'translation-of "unbound variable in code: ~s" var)))

;; init-senv : () -> Senv
;; Page: 96
(define init-senv
  (lambda ()
    (empty-senv)))