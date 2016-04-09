#lang eopl

;; 添加新的feature，比如说在module的body内加入新的语法形式
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; parse ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program ((arbno module-definition) expression) a-program)
    ;; about module
    (module-definition ("module" identifier "interface" interface "body" module-body) a-module-definition)
    (interface ("[" (arbno declaration) "]") simple-iface)
    (declaration (identifier ":" type) val-decl)
    
    (module-body ("[" (arbno definition) "]") defns-module-body)
    (module-body ("letrec"
                  (arbno type identifier "(" identifier ":" type ")" "=" expression)
                  "in" module-body) letrec-module-body)
    (module-body ("let"
                  (arbno identifier "=" expression)
                  "in" module-body) let-module-body)
    
    (definition (identifier "=" expression) val-defn)
    (expression ("from" identifier "take" identifier) qualified-var-exp)
    (type (identifier) named-type)
    (type  ("from" identifier "take" identifier) qualified-type)

    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ":" type ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("letrec" type identifier "(" identifier ":" type ")" "=" expression "in" expression) letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (m-defns body) ;; 先将一些module的定义加载进入env
                 (value-of body
                           (add-module-defns-to-env m-defns (empty-env)))))))

;; add-module-defns-to-env : Listof(Defn) * Env -> Env
;; 这个函数估计要改造啊。
(define add-module-defns-to-env
  (lambda (defns env)
    (if (null? defns)
        env
        (cases module-definition (car defns)
          (a-module-definition (m-name iface m-body) ;; 好吧,这就是一个module的名字,然后是声明的变量,最后是实现
                               (add-module-defns-to-env ;; 先加载一个module,然后加载余下的module,好吧,这就是所谓的递归
                                (cdr defns)
                                (extend-env-with-module
                                 m-name ;; module的名字
                                 (value-of-module-body m-body env) ;; module里面包含的东西
                                 env)))))))
;; value-of-module-body : ModuleBody * Env -> TypedModule
;; 这里干的事情是添加新的feature啊。
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body m-body
      (defns-module-body (defns) ;; 这里的defns应该是一个list
        (simple-module
         (defns-to-env defns env)))
      (letrec-module-body (proc-rtypes proc-names proc-vars proc-vtypes proc-bodies m-body)
                          (add-proc-to-env proc-names proc-vars proc-bodies m-body env))
      (let-module-body (vars exps m-body)
                       (add-binding-to-env vars exps m-body env))
      )))

(define add-binding-to-env
  (lambda (vars exps m-body env)
    (letrec ([extend-env*
              (lambda (vars exps env)
                (if (null? vars) env
                    (let ([val (value-of (car exps) env)])
                      (extend-env* (cdr vars) (cdr exps)
                                   (extend-env (car vars) val env)))))])
      (let ([new-env (extend-env* vars exps env)])
        (value-of-module-body m-body new-env)))))

(define add-proc-to-env
  (lambda  (proc-names proc-vars proc-bodies m-body env) ;; 我们只需要函数的名字，函数的参数，函数体以及定义即可
    (letrec ([extend-env*
              (lambda (proc-names proc-vars proc-bodies env)
                (if (null? proc-names) env
                    (begin
                      (eopl:printf "add-proc-to-env :\n bodies -> ~a\n" (car proc-bodies))
                      (extend-env* (cdr proc-names) (cdr proc-vars) (cdr proc-bodies)
                                   (extend-env-recursively (car proc-names)
                                                           (car proc-vars)
                                                           (car proc-bodies) env)))))])
      (let ([new-env (extend-env* proc-names proc-vars proc-bodies env)])
        (value-of-module-body m-body new-env)))))

;; defns-to-env : Listof(Defn) * Env -> Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env)
        (cases definition (car defns)  
          (val-defn (var exp) ;; 好吧,这个东西实在太厉害了
                    ;(eopl:printf "defns-to-env :\n defns -> ~a\n" defns)
                    (let ([val (value-of exp env)])
                      (let ([new-env (extend-env var val env)])
                        (extend-env var val
                                    (defns-to-env ;; 递归调用
                                      (cdr defns) new-env)))))))))



;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (module-defns body)
                 (type-of body
                          (add-module-defns-to-tenv module-defns (empty-tenv)))))))

;; add-module-defns-to-tenv : Listof(ModuleDefn) * Tenv -> Tenv
;; 好吧，看起来还有很长的一段路要走啊！
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases module-definition (car defns)
               (a-module-definition (m-name expected-iface m-body)
                                    (let ((actual-iface (interface-of m-body tenv)))
                                      (eopl:printf "add-module-defns-to-tenv :\n actual-iface -> ~a\n" actual-iface)
                                      (if (<:-iface actual-iface expected-iface tenv)
                                          (let ((new-tenv
                                                 (extend-tenv-with-module
                                                  m-name
                                                  expected-iface
                                                  tenv)))
                                            (add-module-defns-to-tenv
                                             (cdr defns) new-tenv))
                                          (report-module-doesnt-satisfy-iface
                                           m-name expected-iface actual-iface))))))))

(define report-module-doesnt-satisfy-iface
  (lambda (m-name expected-type actual-type)
    (eopl:pretty-print
     (list 'error-in-defn-of-module: m-name
           'expected-type: expected-type
           'actual-type: actual-type))
    (eopl:error 'type-of-module-defn)))


;; interface-of : ModuleBody * Tenv -> Iface
;; 这个函数是整个项目成功的关键所在
(define interface-of
  (lambda (m-body tenv)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-iface ;; 这是一个数据类型,在iface里面
         (defns-to-decls defns tenv)))
      (letrec-module-body (proc-result-types proc-names proc-vars
                                      bvar-types proc-bodies m-body)
                          (add-proc-to-tenv proc-result-types proc-names bvar-types  m-body tenv))
      (let-module-body (vars exps m-body)
                       (add-binding-to-tenv vars exps m-body tenv))
      )))
(define add-binding-to-tenv
  (lambda (vars exps m-body tenv)
    (letrec [(extend-tenv*
             (lambda (vars exps tenv)
               (if (null? vars) tenv
                   (extend-tenv*
                    (cdr vars) (cdr exps)
                    (extend-tenv (car vars) (type-of (car exps) tenv) tenv)))))]
           (let ([tenv-for-module-body (extend-tenv* vars exps tenv)])
             (interface-of m-body tenv-for-module-body)))))
(define add-proc-to-tenv
  (lambda (proc-result-types proc-names bvar-types m-body tenv)
    ;; 现在无非就是要验证这个式子到底类型正不正确啊。
    (letrec ([extend-tenv*
              (lambda (proc-names bvar-types proc-result-types tenv)
                (if (null? proc-names) tenv
                    (extend-tenv* (cdr proc-names) (cdr bvar-types)
                                  (cdr proc-result-types)
                                  (extend-tenv (car proc-names)
                                               (expand-type (proc-type (car bvar-types)
                                                                       (car proc-result-types))
                                                                       tenv)
                                               tenv))))])
      (let ([tenv-for-module-body
             (extend-tenv* proc-names bvar-types proc-result-types tenv)])
        (interface-of m-body tenv-for-module-body)))))

;; defns-to-decls : Listof(Defn) * Tenv -> Listof(Decl)
(define defns-to-decls
  (lambda (defns tenv)
    (if (null? defns)
        '()
        (cases definition (car defns)
          (val-defn (var-name exp) ;; 变量名和对应的表达式
                    (let ([ty (type-of exp tenv)])
                      (cons
                       (val-decl var-name ty) ;; val-decl也是一个数据类型,表示一个定义的东西
                       (defns-to-decls
                         (cdr defns)
                         (extend-tenv var-name ty tenv)))))))))
;; <:-iface : Iface * Iface * Tenv -> Bool
(define <:-iface
  (lambda (iface1 iface2 tenv)
    (cases interface iface1
      (simple-iface (decls1)
                    (cases interface iface2
                      (simple-iface (decls2)
                                    (<:-decls decls1 decls2 tenv)))))))

;; <:-decls : Listof(Decl) * Listof(Decl) * Tenv -> Bool
(define <:-decls
  (lambda (decls1 decls2 tenv)
    (cond
      [(null? decls2) #t] ;; decls2中声明的东西应该全部实现
      [(null? decls1) #f] ;; 如果decls2不为null,而decls1为null了,显然decls2中声明的东西没有全部实现
      [else
       (let ([name1 (decl->name (car decls1))]
             [name2 (decl->name (car decls2))])
         (if (eqv? name1 name2)
             (and
              (equal?
               (decl->type (car decls1))
               (decl->type (car decls2)))
              (<:-decls (cdr decls1) (cdr decls2) tenv))
             (<:-decls (cdr decls1) decls2 tenv)))]))) ;; 允许这么干的原因是什么呢?也就是允许decls1中的元素多余decls2中的元素

(define type-check
  (lambda (ast)
    (if (type-of-program ast) #t #f)))

(define run
  (lambda (string)
    (let ([ast (scan&parse string)])
      (if (type-check ast) ;; 首先要对程序进行类型检查
          (value-of-program ast)
          (eopl:error "There are something wrong with your program!\n")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; simple-exp ;;;;;;;;;;;;;;;;;;;;;;;;;;
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; data-structures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
(define lookup-qualified-var-in-tenv ;; 在tenv之中寻找qualified-var,话说什么是qualified-var
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

(define lookup-module-name-in-tenv ;; 寻找模块的名字,在tenv之中
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
(define variable-name->maybe-binding-in-tenv ;; 这个函数究竟是干什么的呢?
  (lambda (tenv search-sym)
    (let recur ((tenv tenv))
      (cases type-environment tenv
             (empty-tenv () #f)
             (extend-tenv (name ty saved-tenv) ;; name 变量名 ty 对应的类型 saved-tenv 嵌套的tenv
                          (if (eqv? name search-sym) ;; 如果要搜索的变量名和name匹配的话,返回对应的类型,否则递归
                              ty
                              (recur saved-tenv)))
             (else (recur (tenv->saved-tenv tenv)))))))

;; module-name->maybe-binding-in-tenv : Tenv * Sym -> Maybe(Iface)
(define module-name->maybe-binding-in-tenv ;; 根据模块的名称查找对应的模块,并返回对应的iface(如果存在的话)
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

;; test code
(run "module a interface [f: (int -> int) ] body letrec int g(x: int) = x in [f = g] (from a take f 2)")
(run "module a interface [f: int ] body let g = 1 in [f = g] from a take f")





