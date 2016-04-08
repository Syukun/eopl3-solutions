#lang eopl
(require "./base/data-structure.rkt")
;; 改变语法，使得from m take v变为 m.v，这个貌似也很简单的样子
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; parse ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ;; new-stuff
    (module-var
     (letter (arbno (or letter digit "_" "_" "?")) "."
             (arbno (or letter digit "_" "_" "?")))
     symbol)
    ))

(define the-grammar
  '((program ((arbno module-definition) expression) a-program)
    ;; about module
    (module-definition ("module" identifier "interface" interface "body" module-body) a-module-definition)
    (interface ("[" (arbno declaration) "]") simple-iface)
    (declaration (identifier ":" type) val-decl)
    (module-body ("[" (arbno definition) "]") defns-module-body)
    (definition (identifier "=" expression) val-defn)
    (expression (module-var) qualified-var-exp)
    (type (identifier) named-type)
    (type  (module-var) qualified-type)

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
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body m-body
      (defns-module-body (defns) ;; 这里的defns应该是一个list
        (simple-module
         (defns-to-env defns env))))))

;; defns-to-env : Listof(Defn) * Env -> Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env)
        (cases definition (car defns)
          (val-defn (var exp) ;; 好吧,这个东西实在太厉害了
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
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases module-definition (car defns)
               (a-module-definition (m-name expected-iface m-body)
                                    (let ((actual-iface (interface-of m-body tenv)))
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
(define interface-of
  (lambda (m-body tenv)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-iface ;; 这是一个数据类型,在iface里面
         (defns-to-decls defns tenv))))))

;; defns-to-decls : Listof(Defn) * Tenv -> Listof(Decl)
(define defns-to-decls
  (lambda (defns tenv)
    (if (null? defns)
        '()
        (cases definition (car defns)
          (val-defn (var-name exp)
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
          (value-of-program ast)
          )))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
	   (const-exp (num) (num-val num))
	   (var-exp (var) (apply-env env var))
      (qualified-var-exp (module-var)
                         (eopl:printf "module-var -> ~a\n" module-var)
                         (letrec ([dot-split-string
                                   (lambda (str count) ;; 好吧，这里没有异常处理，因为一定存在.这个字符
                                     (if (char=? #\. (string-ref str count)) (cons (substring str 0 count)
                                                                                   (substring str (+ count 1)))
                                         (dot-split-string str (+ count 1))))])
                           (let ([names (dot-split-string (symbol->string module-var) 0)])
                             (eopl:printf "names -> ~a\n" names)
                             (let ([module (string->symbol (car names))]
                                   [var (string->symbol (cdr names))])
                             (lookup-qualified-var-in-env module var env)))))
			     
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

;; test code

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
	   (qualified-var-exp (module-var)
                              (eopl:printf "module-var -> ~a\n" module-var)
                         (letrec ([dot-split-string
                                   (lambda (str count) ;; 好吧,这里没有异常处理,因为一定存在.这个字符
                                     (if (char=? #\. (string-ref str count)) (cons (substring str 0 count)
                                                                                   (substring str (+ count 1)))
                                         (dot-split-string str (+ count 1))))])
                           (let ([names (dot-split-string (symbol->string module-var) 0)])
                             (eopl:printf "names -> ~a\n" names)
                             (let ([module (string->symbol (car names))]
                                   [var (string->symbol (cdr names))])
                             (lookup-qualified-var-in-tenv module var tenv)))))         

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
	   (qualified-type (modulevar)
			   (list modulevar))
	   )))

;; test code
(run "module m interface [a:int] body [a=1] m.a")


