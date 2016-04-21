#lang eopl
(require "grammer.rkt")
(require "data-structure.rkt")
(require "store.rkt")
(require "class.rkt")
(provide (all-defined-out))
;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp

	   (const-exp (num) (num-val num))

	   (var-exp (var) (deref (apply-env env var)))

	   (diff-exp (exp1 exp2)
		     (let ((val1
			    (expval->num
			     (value-of exp1 env)))
			   (val2
			    (expval->num
			     (value-of exp2 env))))
		       (num-val
			(- val1 val2))))

	   (sum-exp (exp1 exp2)
		    (let ((val1
			   (expval->num
			    (value-of exp1 env)))
			  (val2
			   (expval->num
			    (value-of exp2 env))))
		      (num-val
		       (+ val1 val2))))

	   (zero?-exp (exp1)
		      (let ((val1 (expval->num (value-of exp1 env))))
			(if (zero? val1)
			    (bool-val #t)
			    (bool-val #f))))

	   (if-exp (exp0 exp1 exp2)
		   (if (expval->bool (value-of exp0 env))
		       (value-of exp1 env)
		       (value-of exp2 env)))

      (let-exp (vars exps body)
               (let ((new-env
                      (extend-env
                       vars
                       (map newref (values-of-exps exps env))
                       env)))
		      (value-of body new-env)))

	   (proc-exp (bvars body)
		     (proc-val
		      (procedure bvars body env)))

	   (call-exp (rator rands)
		     (let ((proc (expval->proc (value-of rator env)))
			   (args (values-of-exps rands env)))
		       (apply-procedure proc args)))

	   (letrec-exp (p-names b-varss p-bodies letrec-body)
		       (value-of letrec-body
				 (extend-env-rec** p-names b-varss p-bodies env)))

	   (begin-exp (exp1 exps)
		      (letrec
			  ((value-of-begins
			    (lambda (e1 es)
			      (let ((v1 (value-of e1 env)))
				(if (null? es)
				    v1
				    (value-of-begins (car es) (cdr es)))))))
			(value-of-begins exp1 exps)))

	   (assign-exp (x e)
		       (begin
			 (setref!
			  (apply-env env x)
			  (value-of e env))
			 (num-val 27)))


	   (list-exp (exps)
		     (list-val
		      (values-of-exps exps env)))

	   (empty-exp (exp)
		      (let ((val (value-of exp env)))
			(cases expval val
			       (list-val (vals)
					 (if (null? vals)
					     (bool-val #t)
					     (bool-val #f)))
			       (else
				(eopl:error "empty: error type ~s" exp)))))

	   (car-exp (exp)
		    (let ((val (value-of exp env)))
		      (cases expval val
			       (list-val (vals)
				       (if (null? vals)
					   (eopl:error "car: empty list")
					   (car vals)))
			     (else
			      (eopl:error "car: error type ~s" exp)))))

	   (cdr-exp (exp)
		    (let ((val (value-of exp env)))
		      (cases expval val
			     (list-val (vals)
				       (if (null? vals)
					   (eopl:error "cdr: empty list")
					   (list-val (cdr vals))))
			     (else
			      (eopl:error "cdr: error type ~s" exp)))))

	   (cons-exp (arg1 arg2)
		     (let ((val1 (value-of arg1 env))
			   (val2 (value-of arg2 env)))
		       (cases expval val2
			      (list-val (vals)
					(list-val (cons val1 vals)))
			      (else
			       (eopl:error "cons: error type ~s" arg2)))))

	   ;; new cases for CLASSES language
	   (new-object-exp (class-name rands)
			   (let ([args (values-of-exps rands env)]
				 [obj (new-object class-name)])
			     (apply-method
			      (find-method class-name 'initialize)
			      obj
			      args)
			     obj))

	   (self-exp ()
		     (apply-env env '%self))

	   (method-call-exp (obj-exp method-name rands)
			    (let ((args (values-of-exps rands env))
				  (obj (value-of obj-exp env)))
			      (apply-method
			       (find-method (object->class-name obj) method-name)
			       obj
			       args)))

	   (super-call-exp (method-name rands)
			   (let ((args (values-of-exps rands env))
				 (obj (apply-env env '%self)))
			     (apply-method
			      (find-method (apply-env env '%super) method-name)
			      obj
			      args)))
	   )))

(define values-of-exps
    (lambda (exps env)
      (map
        (lambda (exp) (value-of exp env))
        exps)))

;; apply-procedure : Proc * Listof(ExpVal) -> ExpVal
(define apply-procedure
    (lambda (proc1 args)
      (cases proc proc1
        (procedure (vars body saved-env)
          (let ((new-env
                  (extend-env
                    vars
                    (map newref args)
                    saved-env)))
            (value-of body new-env))))))

;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (class-decls body)
                 (initialize-class-env! class-decls)
                 (value-of body (init-env))))))

