#lang eopl
(require "grammer.rkt")
(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 在这里的话，我们算是看到了划分模块的好处了。
;; 让一些类型相近的东西放置在一块，使得文件更好的划分。
;; 这个文件里面主要是关于data-strucure的一些事情。
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; data structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype expval expval? ;; 值的类型
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?)))

;;; extractors:
(define expval->num
  (lambda (v)
    (cases expval v
           (num-val (num) num)
           (else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
           (bool-val (bool) bool)
           (else (expval-extractor-error 'bool v)))))

(define expval->proc
  (lambda (v)
    (cases expval v
           (proc-val (proc) proc)
           (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;
(define-datatype proc proc? ;; 好吧,所谓的过程
  (procedure
   (bvar symbol?)
   (body expression?)
   (env environment?)))

;;;;;;;;;;;;;;;; module values ;;;;;;;;;;;;;;;;
(define-datatype typed-module typed-module? ;; 模块类型
  (simple-module
   (bindings environment?))
  (proc-module
   (bvar symbol?)
   (body module-body?)
   (saved-env environment?))
  )

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval expval?)
   (saved-env environment?))
  (extend-env-recursively
   (id symbol?)
   (bvar symbol?)
   (body expression?)
   (saved-env environment?))
  (extend-env-with-module
   (m-name symbol?)
   (m-val typed-module?)
   (saved-env environment?)
   ))

;;;;;;;;;;;;;;;; initial environment ;;;;;;;;;;;;;;;;

;; initial-value-env : module-env -> environment

;; (init-env m-env) builds an environment in which i is bound to the
;; expressed value 1, v is bound to the expressed value 5, and x is
;; bound to the expressed value 10, and in which m-env is the module
;; environment.
(define inital-value-env
  (lambda (m-env)
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env m-env))))))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

;; for variables bound by extend-env or extend-env-recursively

(define apply-env ;; 查找对应的值 
  (lambda (env search-sym)
    (cases environment env
	   (empty-env ()
		      (eopl:error 'apply-env "No value binding for ~s" search-sym))
	   (extend-env (bvar bval saved-env)
		       (if (eqv? search-sym bvar)
			   bval
			   (apply-env saved-env search-sym)))
	   (extend-env-recursively
	    (id bvar body saved-env) ;; id 表示函数的名字
	    (if (eqv? search-sym id)
		(proc-val (procedure bvar body env))
		(apply-env saved-env search-sym)))
	   (extend-env-with-module (m-name m-val saved-env)
				   (begin
				     (eopl:printf "\nhaha: ~s ~s\n" m-name search-sym)
				     (apply-env saved-env search-sym)) ))))

;; for names bound by extend-env-with-module

;; lookup-module-name-in-env : Sym * Env -> Typed-Module
(define lookup-module-name-in-env 
  (lambda (m-name env)
    (cases environment env
	   (empty-env ()
		      (eopl:error 'lookup-module-name-in-env
				  "No module binding for ~s" m-name))
	   (extend-env (bvar bval saved-env)
		       (lookup-module-name-in-env m-name saved-env))
	   (extend-env-recursively  (id bvar body saved-env)
				    (lookup-module-name-in-env m-name saved-env))
	   (extend-env-with-module (m-name1 m-val saved-env)
	    (if (eqv? m-name1 m-name)
		m-val
		(lookup-module-name-in-env m-name saved-env))))))

;; lookup-qualified-var-in-env : Sym * Sym * Env -> ExpVal
(define lookup-qualified-var-in-env ;; qualified var究竟是什么鬼? 有意思啊。
  (lambda (m-name var-name env) 
    (let ((m-val (lookup-module-name-in-env m-name env)))
					; (pretty-print m-val)
      (cases typed-module m-val
	     (simple-module (bindings)
			    (apply-env bindings var-name))
	     (proc-module (bvar body saved-env)
			  (eopl:error 'lookup-qualified-var
				      "can't retrieve variable from ~s take ~s from proc module"
				      m-name var-name))))))

(define expand-type (lambda (ty tenv) ty))
(define expand-iface (lambda (m-name iface tenv) iface))



