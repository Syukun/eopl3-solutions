#lang eopl
(require "translator.rkt")
(require "parse.rkt")
(require "helper.rkt")
(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   interpreter
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;
(define identifier? symbol?)

;; nameless-environment? : SchemeVal -> Bool
;; Page: 99
(define nameless-environment?
  (lambda (x)
    ((list-of expval?) x)))

;; empty-nameless-env : () -> Nameless-env
;; Page: 99
(define empty-nameless-env
  (lambda ()
    '()))

;; empty-nameless-env? : Nameless-env -> Bool
(define empty-nameless-env? 
  (lambda (x)
    (null? x)))

;; extend-nameless-env : ExpVal * Nameless-env -> Nameless-env
;; Page: 99
(define extend-nameless-env
  (lambda (val nameless-env)
    (cons val nameless-env)))

;; apply-nameless-env : Nameless-env * Lexaddr -> ExpVal
;; Page: 99
(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref nameless-env n)))


;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val 
   (proc proc?))
  (pair-val
   (car expval?) ;; It's great!
   (cdr expval?))
  (emptylist-val))

;;; extractors:

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
	   (num-val (num) num)
	   (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
	   (bool-val (bool) bool)
	   (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
	   (proc-val (proc) proc)
	   (else (expval-extractor-error 'proc v)))))

(define expval->pair
  (lambda (v)
    (cases expval v
	   (pair-val (car cdr) ;;Notes: pair-val consists of two components,one is car,another is cdr.
		     (cons car cdr))
	   (else (expval-extractor-error 'pair v)))))

(define expval->car
  (lambda (v)
    (cases expval v
	   (pair-val (car cdr) car)
	   (else (expval-extractor-error 'car v)))))

(define expval->cdr
  (lambda (v)
    (cases expval v
	   (pair-val (car cdr) cdr)
	   (else (expval-extractor-error 'cdr v)))))

(define expval->null?
  (lambda (v)
    (cases expval v
	   (emptylist-val () #t)
	   (else #f))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
		variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;


;; proc? : SchemeVal -> Bool
;; procedure : Exp * Nameless-env -> Proc
(define-datatype proc proc?
  (procedure
   ;; in LEXADDR, bound variables are replaced by %nameless-vars, so
   ;; there is no need to declare bound variables.
   ;; (bvar symbol?)
   (body expression?)
   ;; and the closure contains a nameless environment
   (env nameless-environment?)))


;; value-of-program : Nameless-program -> ExpVal
;; Page: 100
(define value-of-program
  (lambda (pgm)
    (begin
      (print "value-of-program : pgm --> " pgm)
      (cases program pgm
	     (a-program (exp1)
			(begin
			  (print "value-of-program : exp1 --> " exp1)
			  (value-of exp1 (init-nameless-env))))))))

(define init-nameless-env
  (lambda ()
    (empty-nameless-env)))

(define value-of
  (lambda (exp nameless-env)
    (begin
      ;(print "value-of : exp --> " exp)
      ;(print "value-of : nameless-env --> " nameless-env)
      (cases expression exp
        (const-exp (num) (num-val num))
        
        (diff-exp (exp1 exp2)
                  (let ((val1
                         (expval->num
                          (value-of exp1 nameless-env)))
                        (val2
                         (expval->num
                          (value-of exp2 nameless-env))))
                    (num-val
                     (- val1 val2))))
        
        (zero?-exp (exp1)
                   (let ((val1 (expval->num (value-of exp1 nameless-env))))
                     (if (zero? val1)
                         (bool-val #t)
                         (bool-val #f))))
        
        (if-exp (exp0 exp1 exp2)
                (if (expval->bool (value-of exp0 nameless-env))
                    (value-of exp1 nameless-env)
                    (value-of exp2 nameless-env)))
        
        (call-exp (rator rand)
                  (begin
                    (print "call-exp : rator --> " rator)
                    (print "call-exp : rand --> " rand)
                    (let ((proc (expval->proc (value-of rator nameless-env)))
                          (arg (map (lambda (x) (value-of x nameless-env)) rand)))
                      (begin
                        (print "call-exp : proc --> " proc)
                        (print "call-exp : arg --> " arg)
                        (apply-procedure proc arg)))))
        
        ;;new stuff
        (cons-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 nameless-env))
                      (val2 (value-of exp2 nameless-env)))
                    (pair-val val1 val2)))
        (emptylist-exp ()
                       (emptylist-val))
        
        (nameless-unpack-exp (values body)
                             (let [(vlist (value-of values nameless-env))]
                               (begin
                               ;(print "value-of.unpack-exp : vlist --> " vlist)
                               (print "value-of.unpack-exp : body-env --> "  (extend-nameless-env-list vlist nameless-env))
                               (value-of body (extend-nameless-env-list vlist nameless-env)))))
        (nameless-letrec-exp (f-body body)
                             (begin
                               (print "value-of.nameless-letrec-exp : f-body --> " f-body)
                               (print "value-of.nameless-letrec-exp : body --> " body)
                               (print "value-of.nameless-letrec-exp : nameless-env --> " nameless-env)
                               (let ((val (value-of f-body nameless-env)))
                                 (value-of body (extend-nameless-env val nameless-env)))))
      
        (cond-exp (conds acts)
                  (cond-val conds acts nameless-env))
        
        (nameless-var-exp (n)
                          (apply-nameless-env nameless-env n))

        (nameless-let-exp (exp1 body)
                          (let ((val (value-of exp1 nameless-env)))
                            (begin
                              (print "value-of.nameless-let-exp : val --> " val)
                              (print "value-of.nameless-let-exp : body --> " body)
                              (value-of body
                                        (extend-nameless-env val nameless-env)))))
      
        (nameless-proc-exp (body)
                           (proc-val
                            (procedure body nameless-env)))
        
        (else (eopl:error "Illegal expression in translated code: ~s" exp))
        
      ))))
(define (extend-nameless-env-list pair-exp senv)
  (begin
    (print "extend-nameless-env-list : pair-exp --> " pair-exp)
    (if (expval->null? pair-exp) senv
        (extend-nameless-env-list (expval->cdr pair-exp) (extend-nameless-env (expval->car pair-exp) senv)))))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure
  (lambda (proc1 arg)
    (cases proc proc1
           (procedure (body saved-env)
                      (value-of body (extend-nameless-env* arg saved-env))))))

(define (extend-nameless-env* varlist senv)
  (if (null? varlist) senv
      (extend-nameless-env* (cdr varlist) (extend-nameless-env (car varlist) senv))))

;;new stuff
(define cond-val
  (lambda (conds acts nameless-env)
    (cond ((null? conds)
	   (eopl:error 'cond-val "No conditions got into #t"))
	  ((expval->bool (value-of (car conds) nameless-env))
	   (value-of (car acts) nameless-env))
	  (else
	   (cond-val (cdr conds) (cdr acts) nameless-env)))))