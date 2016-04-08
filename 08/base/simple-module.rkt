#lang eopl
(require "parse.rkt")
(require "data-structure.rkt")
(provide (all-defined-out))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
	   (const-exp (num) (num-val num))
	   (var-exp (var) (apply-env env var))
	   (qualified-var-exp (m-name var-name)
			      (lookup-qualified-var-in-env m-name var-name env))
	   (diff-exp (exp1 exp2)
		     (let ([val1 (expval->num (value-of exp1 env))]
			   [val2 (expval->num (value-of exp2 env))])
		       (num-val	(- val1 val2))))
	   (zero?-exp (exp1)
		      (let ([val1 (expval->num (value-of exp1 env))])
			(if (zero? val1)
			    (bool-val #t)
			    (bool-val #f))))
	   (if-exp (exp0 exp1 exp2)
		   (if (expval->bool (value-of exp0 env))
		       (value-of exp1 env)
		       (value-of exp2 env)))
	   (let-exp (var exp1 body)
		    (let ([val (value-of exp1 env)])
		      (let ([new-env (extend-env var val env)])
			(value-of body new-env))))

	   (proc-exp (bvar ty body)
		     (proc-val (procedure bvar body env)))
	   (call-exp (rator rand)
		     (let ([proc (expval->proc (value-of rator env))]
			   [arg  (value-of rand env)])
		       (apply-procedure proc arg)))

	   (letrec-exp (ty1 proc-name bvar ty2 proc-body letrec-body)
		       (value-of letrec-body (extend-env-recursively proc-name bvar proc-body env)))

	   )))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure
  (lambda (proc1 arg)
    (cases proc proc1
	   (procedure (var body saved-env)
		      (value-of body (extend-env var arg saved-env))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; type ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-of : Exp * Tenv -> Type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
           (const-exp (num) (int-type))

           (diff-exp (exp1 exp2)
                     (let ([type1 (type-of exp1 tenv)]
                           [type2 (type-of exp2 tenv)])
		       (check-equal-type! type1 (int-type) exp1)
		       (check-equal-type! type2 (int-type) exp2)
		       (int-type)))

	   (zero?-exp (exp1)
		      (let ([type1 (type-of exp1 tenv)])
			(check-equal-type! type1 (int-type) exp1)
			(bool-type)))

	   (if-exp (exp1 exp2 exp3)
		   (let ([ty1 (type-of exp1 tenv)]
			 [ty2 (type-of exp2 tenv)]
			 [ty3 (type-of exp3 tenv)])
		     (check-equal-type! ty1 (bool-type) exp1)
		     (check-equal-type! ty2 ty3 exp)
		     ty2))

	   (var-exp (var) (apply-tenv tenv var))

	   ;; lookup-qualified-var-in-tenv defined on page 285.
	   (qualified-var-exp (m-name var-name)
			      (lookup-qualified-var-in-tenv m-name var-name tenv))

	   (let-exp (var exp1 body)
		    (let ([rhs-type (type-of exp1 tenv)])
		      (type-of body (extend-tenv var rhs-type tenv))))

	   (proc-exp (bvar bvar-type body)
		     (let ([expanded-bvar-type (expand-type bvar-type tenv)])
		       (let ([result-type (type-of body (extend-tenv bvar expanded-bvar-type tenv))])
			 (proc-type expanded-bvar-type result-type))))

	   (call-exp (rator rand)
		     (let ([rator-type (type-of rator tenv)]
			   [rand-type  (type-of rand tenv)])
		       (cases type rator-type
			      (proc-type (arg-type result-type)
					 (begin
					   (check-equal-type! arg-type rand-type rand)
					   result-type))
			      (else (eopl:error 'type-of
					   "Rator not a proc type:~%~s~%had rator type ~s"
					   rator (type-to-external-form rator-type))))))

	   (letrec-exp (proc-result-type proc-name bvar bvar-type proc-body letrec-body)
		       (let ([tenv-for-letrec-body (extend-tenv proc-name  (expand-type (proc-type bvar-type proc-result-type) tenv) tenv)])
			 (let ([proc-result-type (expand-type proc-result-type tenv)]
			       [proc-body-type (type-of proc-body  (extend-tenv bvar (expand-type bvar-type tenv) tenv-for-letrec-body))])
			   (check-equal-type! proc-body-type proc-result-type proc-body)
			   (type-of letrec-body tenv-for-letrec-body))))

	   )))

;; check-equal-type! : Type * Type * Exp -> Unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp)
        #f)))

;; report-unequal-types : Type * Type * Exp -> Unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
		"Types didn't match: ~s != ~a in~%~a"
		(type-to-external-form ty1)
		(type-to-external-form ty2)
		exp)))

(define type-to-external-form
  (lambda (ty)
    (cases type ty
	   (int-type () 'int)
	   (bool-type () 'bool)
	   (proc-type (arg-type result-type)
		      (list
		       (type-to-external-form arg-type)
		       '->
		       (type-to-external-form result-type)))
	   (named-type (name) name)
	   (qualified-type (modname varname)
			   (list 'from modname 'take varname))
	   )))


