#lang eopl
(require "parse.rkt")
(provide (all-defined-out))
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


(define-datatype type-environment type-environment? ;; 这个玩意主要用于类型推断
  (empty-tenv)
  (extend-tenv
   (bvar symbol?)
   (bval type?)
   (saved-tenv type-environment?))
  (extend-tenv-with-module
   (name symbol?)
   (interface interface?)
   (saved-tenv type-environment?))
  )
;;;;;;;;;;;;;;;; procedures for looking things up tenvs ;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;; lookup or die

;; lookup-qualified-var-in-tenv : Sym * Sym * Tenv -> Type
(define lookup-qualified-var-in-tenv ;; 在tenv之中寻找qualified-var，话说什么是qualified-var
  (lambda (m-name var-name tenv) ;; 先根据module的名字找到对应的interface
    (let ((iface (lookup-module-name-in-tenv tenv m-name)))
      (cases interface iface
             (simple-iface (decls) ;; 然后在interface之中找到对应变量的类型
                           (lookup-variable-name-in-decls var-name decls)) ))))

(define lookup-variable-name-in-tenv ;; 在tenv之中寻找变量名
  (lambda (tenv search-sym)
    (let ((maybe-answer
           (variable-name->maybe-binding-in-tenv tenv search-sym)))
      (if maybe-answer maybe-answer
          (raise-tenv-lookup-failure-error 'variable search-sym tenv)))))

(define lookup-module-name-in-tenv ;; 寻找模块的名字，在tenv之中
  (lambda (tenv search-sym)
    (let ((maybe-answer
           (module-name->maybe-binding-in-tenv tenv search-sym)))
      (if maybe-answer maybe-answer
          (raise-tenv-lookup-failure-error 'module search-sym tenv)))))

(define apply-tenv lookup-variable-name-in-tenv)

(define raise-tenv-lookup-failure-error
  (lambda (kind var tenv)
    (eopl:pretty-print
     (list 'tenv-lookup-failure: (list 'missing: kind var) 'in:
           tenv))
    (eopl:error 'lookup-variable-name-in-tenv)))

(define lookup-variable-name-in-decls ;; 查找变量名-->在declare之中寻找变量名对应的类型
  (lambda (var-name decls0)
    (let loop ((decls decls0))
      (cond
       ((null? decls)
        (raise-lookup-variable-in-decls-error! var-name decls0))
       ((eqv? var-name (decl->name (car decls)))
        (decl->type (car decls)))
       (else (loop (cdr decls)))))))

(define raise-lookup-variable-in-decls-error!
  (lambda (var-name decls)
    (eopl:pretty-print
     (list 'lookup-variable-decls-failure:
           (list 'missing-variable var-name)
           'in:
           decls))

    (eopl:error 'lookup-variable-error)))

;;;;;;;;;;;;;;;; lookup or return #f.
;; variable-name->maybe-binding-in-tenv : Tenv * Sym -> Maybe(Type)
(define variable-name->maybe-binding-in-tenv ;; 这个函数究竟是干什么的呢？
  (lambda (tenv search-sym)
    (let recur ((tenv tenv))
      (cases type-environment tenv
             (empty-tenv () #f)
             (extend-tenv (name ty saved-tenv) ;; name 变量名 ty 对应的类型 saved-tenv 嵌套的tenv
                          (if (eqv? name search-sym) ;; 如果要搜索的变量名和name匹配的话，返回对应的类型，否则递归
                              ty
                              (recur saved-tenv)))
             (else (recur (tenv->saved-tenv tenv)))))))

;; module-name->maybe-binding-in-tenv : Tenv * Sym -> Maybe(Iface)
(define module-name->maybe-binding-in-tenv ;; 根据模块的名称查找对应的模块，并返回对应的iface（如果存在的话）
  (lambda (tenv search-sym)
    (let recur ((tenv tenv))
      (cases type-environment tenv
             (empty-tenv () #f)
             (extend-tenv-with-module (name m-type saved-tenv)
                                      (if (eqv? name search-sym)
                                          m-type
                                          (recur saved-tenv)))
             (else (recur (tenv->saved-tenv tenv)))))))

;; assumes tenv is non-empty.
(define tenv->saved-tenv ;; 确实是一个非常简单的一个东西
  (lambda (tenv)
    (cases type-environment tenv
           (empty-tenv ()
                       (eopl:error 'tenv->saved-tenv
                                   "tenv->saved-tenv called on empty tenv"))
           (extend-tenv (name ty saved-tenv) saved-tenv)
           (extend-tenv-with-module (name m-type saved-tenv) saved-tenv)
           )))

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
	    (id bvar body saved-env)
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
(define lookup-qualified-var-in-env ;; qualified var究竟是什么鬼？ 有意思啊。
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

;;;;;;;;;;;;;;;;;;;;;; about decl
;; decl->name : Declaration -> Name
;; 获得声明的名字
(define decl->name
  (lambda (decl)
    (cases declaration decl
	   (val-decl (name ty) name))))

(define decl->type
  (lambda (decl)
    (cases declaration decl
	   (val-decl (name ty) ty))))


