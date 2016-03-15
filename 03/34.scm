(load-relative "../libs/init.scm")
;; ex-34
;; The procedural representation of environments.

;; empty-env : () -> Env
(define empty-env
  (lambda ()
    (lambda (search-var) 
      (report-no-binding-found search-var))))
  
;; extend-env : Var * Schemeval * Env -> Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (if (eqv? search-var saved-var)
          saved-val
          (apply-env saved-env search-var)))))

;; exten-env-rec
(define extend-env-rec
  (lambda (p-name b-var p-body saved-env)
    (lambda (search-var)
      (if (eqv? search-var p-name)
	  (proc-val (procedure b-var p-body env))
	  (apply-env saved-env search-var)))))

 ;; apply-env : Env * Var -> Schemeval
(define apply-env
  (lambda (env search-var) 
    (env search-var)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
  
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

;;;;;;;;;;;;;;;;;expval;;;;;;;;;
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?)))



