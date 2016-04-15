#lang eopl
;; 在11题的基础上，添加field的安全性

(define identifier? symbol?)
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
  '((program ((arbno class-decl) expression) a-program)

    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("+" "(" expression "," expression ")")
     sum-exp)

    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    (expression (identifier) var-exp)

    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    (expression
     ("letrec"
      (arbno identifier "(" (separated-list identifier ",") ")"
	     "=" expression)
      "in" expression)
     letrec-exp)

    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)
    ;; set 表达式也是非常重要的!
    (expression
     ("set" identifier "=" expression)
     assign-exp)
    ;; 这个玩意对于实现queue十分重要
    (expression
     ("list" "(" (separated-list expression ",") ")" )
     list-exp)

    ;; new stuff for list
    (expression
     ("empty?" "(" expression ")" )
     empty-exp)

    (expression
     ("car" "(" expression ")" )
     car-exp)

    (expression
     ("cdr" "(" expression ")" )
     cdr-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    ;; new productions for oop
    (class-decl
     ("class" identifier
      "extends" identifier
      (arbno field-decl)
      (arbno method-decl)
      )
     a-class-decl)
    
    (field-decl
     ("*" security identifier) a-field-decl) ;; 不要在意语法这个玩意啦！
     
    (method-decl
     (security identifier
      "("  (separated-list identifier ",") ")" ; method formals
      expression
      )
     a-method-decl)

    (security ("public") public-security)
    (security ("private") private-security)
    (security ("protect") protect-security)

    (expression
     ("new" identifier "(" (separated-list expression ",") ")")
     new-object-exp)

    ;; this is special-cased to prevent it from mutation
    (expression
     ("self")
     self-exp)

    (expression
     ("send" expression identifier
      "("  (separated-list expression ",") ")")
     method-call-exp)

    (expression
     ("super" identifier    "("  (separated-list expression ",") ")")
     super-call-exp)

    ;; fieldref 表达式, 不就是获取某个变量的值嘛
    (expression ("fieldref" expression identifier) fieldref-exp)
    ;; fieldset 表达式
    (expression ("fieldset" expression identifier "=" expression) fieldset-exp)
    
    ;; superfieldref
    (expression ("superfieldref" expression identifier) superfieldref-exp)
    ;; superfieldset
    (expression ("superfieldset" expression identifier "=" expression) superfieldset-exp)

    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

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
                       (eopl:printf "value-of :\n obj-exp -> ~a\n method-name -> ~a\n rands -> ~a\n" obj-exp method-name rands)
                       (let ([args (values-of-exps rands env)]
                             [obj (value-of obj-exp env)])
                         (let ([meth (find-method (object->class-name obj) method-name)])
                           (let ([sec (method->security meth)]) ;; 首先要判断这个玩意的安全性
                             (cond
                               [(eqv? sec 'public) (apply-method meth obj args)] ;; 如果是public方法,那么什么东西都可以调用
                               [(eqv? sec 'private)
                                (let ([maybe-self (lookup-self-and-super env '%self)])
                                  (if maybe-self ;; 这说明了是在class的内部函数调用自身的一个私有的函数
                                      (apply-method meth obj args)
                                      (eopl:error "The method is a private method!\n")))]
                               [(eqv? sec 'protect) ;; 好吧,这个玩意有点挑战度
                                (let [(maybe-self (lookup-self-and-super env '%self))]
                                  (if maybe-self ;; 这说明了是在一个class的函数的内部调用自身的一个protect函数
                                      (apply-method meth obj args)
                                      (eopl:error "~s is a protect method!\n" method-name)))])))))
                            

	   (super-call-exp (method-name rands)
			   (let ([args (values-of-exps rands env)]
				 [obj (apply-env env '%self)])
                             (let ([meth (find-method (apply-env env '%super) method-name)])
                               ;; 接下来要进行安全性的判定啦
                               (let ([sec (method->security meth)]) ;; 获得这个方法的安全性
                                 (cond
                                   [(eqv? sec 'private) (eopl:error "~a is a private method in super class!\n" method-name)]
                                   ;; 父类的protect方法和public方法都可以自由调用
                                   [else (apply-method meth obj args)])))))


      ;; fieldref 引用变量的值
      (fieldref-exp (exp1 id)
                    (let ([a-ref (find-field-ref id (value-of exp1 env) env)])
                      (deref a-ref)))
      
      (fieldset-exp (exp1 f-name exp2)
                    (let ([a-ref (find-field-ref f-name (value-of exp1 env) env)])
                      (setref! a-ref (value-of exp2 env))))

      (superfieldref-exp (exp1 f-name)
                         (let ([the-object (value-of exp1 env)])
                           (let ([the-ref (find-superfield-ref f-name the-object env)])
                             (deref the-ref))))
      (superfieldset-exp (exp1 f-name exp2)
                         (let ([the-object (value-of exp1 env)])
                           (let ([the-ref (find-superfield-ref f-name the-object env)])
                             (setref! the-ref (value-of exp2 env)))))
			
	   )))

(define find-superfield-ref
        (lambda (f-name the-object env)
          (cases object the-object
            (an-object (c-name fields)
                       (cases class (lookup-class c-name)
                         (a-class (s-name f-names m-env)
                                  (cases class (lookup-class s-name)
                                    (a-class (s-name f-names m-env) ;; 找到父类的定义
                                             (let ([maybe-ref (lookup-field f-name f-names fields env)])
                                               (if maybe-ref maybe-ref
                                                   (eopl:error "~a does not exist in superclass!\n" f-name)))))))))))
(define lookup-field
  (lambda (f-name f-names fields env)
    (if (null? f-names) #f
        (if (eqv? f-name (caar f-names))
             (let ([sec (cdar f-names)]) ;; 得到这个变量的安全性修饰词
               (cond
                 [(eqv? sec 'public) (car fields)]
                 [(eqv? sec 'private) (eopl:error "* ~a is a private field!\n" f-name)]
                 [(eqv? sec 'protect)
                  (let ([maybe-self (lookup-self-and-super env '%self)])
                    (if maybe-self ;; 这说明了是在class的内部函数引用父类的变量
                        (car fields) ;; protect修饰的变量可以在类的内部引用
                        (eopl:printf "* ~a is a protect field!\n")))] ))
             (lookup-field f-name (cdr f-names) (cdr fields) env)))))
                                                       
          

(define find-field-ref
  (lambda (search-field the-object env)
    (cases object the-object
      (an-object (c-name fields) ;; 现在重要的是找到对应的引用值
                 (let ([the-class (lookup-class c-name)]) ;; 先找到对应的class
                   (cases class the-class
                     (a-class (s-name f-names m-env)
                              (letrec ([lookup-field-ref
                                        (lambda (search-field lofn lor)
                                          (if (null? lofn) (eopl:error "~a does not exist!\n" search-field)
                                              (if (eqv? search-field (caar lofn)) 
                                                  (let ([sec (cdar lofn)])
                                                    (cond
                                                      [(eqv? sec 'public) (car lor)]
                                                      [(eqv? sec 'private)
                                                       (let ([maybe-self (lookup-self-and-super env '%self)])
                                                         (if maybe-self ;; 这说明了是在class的内部函数调用自身的一个私有的函数
                                                             (car lor)     
                                                             (eopl:error "~a is a private field!\n" search-field)))]
                                                      [(eqv? sec 'protect)
                                                       (let ([maybe-self (lookup-self-and-super env '%self)])
                                                         (if maybe-self ;; 这说明了是在class的内部函数调用自身的一个私有的函数
                                                             (car lor)     
                                                             (eopl:error "~a is a protect field!\n" search-field)))]))
                                              (lookup-field-ref (search-field (cdr lofn) (cdr lor))))))]) 
                                (lookup-field-ref search-field f-names fields)))))))))

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

(define-datatype object object?
  (an-object
   (class-name identifier?)
   (fields (list-of reference?))))

;; new-object : ClassName -> Obj
(define new-object
  (lambda (class-name)
    (an-object
     class-name
     (map
      (lambda (field-name)
        (newref (list 'uninitialized-field field-name)))
      (class->field-decls (lookup-class class-name))))))

(define-datatype method method?
  (a-method
   (vars (list-of identifier?))
   (sec identifier?) ;; 用来描述这个方法的安全性
   (body expression?)
   (super-name identifier?)
   (field-names (list-of pair?)))) ;; 简化一点吧


(define method->security
  (lambda (meth)
    (cases method meth
      (a-method (vars sec body s-name f-names) sec))))
(define method->super-name
  (lambda (meth)
    (cases method meth
      (a-method (vars sec body s-name f-names) s-name))))

;; apply-method : Method * Obj * Listof(ExpVal) -> ExpVal
(define apply-method
  (lambda (m self args)
    (cases method m
      (a-method (vars sec body super-name fields)
                (value-of body
                          (extend-env vars (map newref args)
                                      (extend-env-with-self-and-super
                                       self super-name
                                       (extend-env (fields->name fields) (object->fields self)
                                                   (empty-env)))))))))
(define fields->name
  (lambda (fields)
    (if (null? fields) '()
        (cons (caar fields) (fields->name (cdr fields))))))

;; the-calss-env : ClassEnv
(define the-class-env '())

;; add-to-class-env! : ClassName * Class -> Unspecified
(define add-to-calss-env!
  (lambda (class-name class)
    (set! the-class-env
          (cons
           (list class-name class)
           the-class-env))))

;; lookup-class : ClassName -> Class
(define lookup-class
  (lambda (name)
    (let ([maybe-pair (assq name the-class-env)])
      (if maybe-pair (cadr maybe-pair)
          (report-unknown-class name)))))

(define report-unknown-class
  (lambda (name)
    ;(eopl:printf "the-class-env -> ~a\n" the-class-env)
    (eopl:error 'lookup-class "Unknown class ~s" name)))

(define-datatype class class?
  (a-class
   (super-name (maybe identifier?))
   (fields (list-of pair?)) ;; 这里的fields包括了名字和修饰的关键字
   (method-env method-environment?)))

;;;;;;;;;;;;;;;; method environments ;;;;;;;;;;;;;;;;

;; a method environment looks like ((method-name method) ...)
(define method-environment?
  (list-of
   (lambda (p)
     (and
      (pair? p)
      (symbol? (car p))
      (method? (cadr p))))))

;; initialize-class-env! : ClassDecl -> Unspecified
(define initialize-class-env!
  (lambda (c-decls) ;; c-decls 代表的是类的定义
    (set! the-class-env
          (list
           (list 'object (a-class #f '() '()))))
           (for-each initialize-class-decl! c-decls)))

;; initialize-class-decl! : ClassDecl -> Unspecified
(define initialize-class-decl!
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (c-name s-name f-decls m-decls) ;; f-decls 代表field的定义
                    (eopl:printf "initialize-class-decl! :\n s-name -> ~a\n the-class-env -> ~a\n" s-name the-class-env)
                    (eopl:printf "c-name -> ~a\n" c-name)
                    (let ([fields
                           (append-fields
                            (class->field-decls (lookup-class s-name))
                            (convert-f-decls f-decls))])
                      (add-to-calss-env!
                       c-name ;; 类的名字
                       (a-class s-name fields
                                (merge-method-envs
                                 (class->method-env (lookup-class s-name))
                                 (method-decls->method-env
                                  m-decls s-name fields)))))))))
(define convert-f-decls
  (lambda (f-decls) ;; f-decls 是一个list
    (map (lambda (f-decl)
           (cases field-decl f-decl
             (a-field-decl (sec id) (cons id (sec-to-external-form sec))))) f-decls)))

;; append-field-names :
;;  Listof(FieldName) * Listof(FieldName) -> Listof(FieldName)
(define append-fields ;; 好吧，还要修改这个函数
  (lambda (super-fields new-fields)
    (cond
      [(null? super-fields) new-fields]
      [else
       (cons
        (if (field-name-exist? (caar super-fields) new-fields)
            (list (fresh-identifier (caar super-fields)) (cadr super-fields))
            (car super-fields))
        (append-fields
         (cdr super-fields) new-fields))])))

(define field-name-exist?
  (lambda (name field-names)
    (if (null? field-names) #f
        (if (eqv? name (caar field-names)) #t
            (field-name-exist? name (cdr field-names))))))

;; find-method : Sym * Sym -> Method
(define find-method
  (lambda (c-name name)
    (let ([m-env (class->method-env (lookup-class c-name))])
      (let ([maybe-pair (assq name m-env)])
        (if (pair? maybe-pair) (cadr maybe-pair)
            (report-method-not-found name))))))

(define report-method-not-found
  (lambda (name)
    (eopl:error 'find-method "unknown method ~s" name)))

;; method-decls -> method-env
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (eopl:printf "field-names -> ~a\n" field-names)
    (map
     (lambda (m-decl)
       (cases method-decl m-decl
         (a-method-decl (sec method-name vars body)
                        (list method-name ;; 方法的名字
                              (a-method vars (sec-to-external-form sec) body super-name field-names)))))
     m-decls)))

(define sec-to-external-form
  (lambda (sec)
           (cases security sec
             (public-security () 'public)
             (private-security () 'private)
             (protect-security () 'protect))))

;; merge-method-envs : MethodEnv * MethodEnv -> MethodEnv
(define merge-method-envs
  (lambda (super-m-env new-m-env)
    (append new-m-env super-m-env)))

;;;;;;;;;;;;;;;; selectors ;;;;;;;;;;;;;;;;

(define class->super-name
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name field-decls method-env)
		    super-name))))

(define class->field-decls
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name field-decls method-env)
		    field-decls))))

(define class->method-env
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name  field-decls method-env)
		    method-env))))


(define object->class-name
  (lambda (obj)
    (cases object obj
	   (an-object (class-name fields)
		      class-name))))

(define object->fields
  (lambda (obj)
    (cases object obj
	   (an-object (class-decl fields)
		      fields))))

(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
	(symbol->string identifier)
	"%"             ; this can't appear in an input identifier
	(number->string sn))))))

(define maybe
  (lambda (pred)
    (lambda (v)
      (or (not v) (pred v)))))

;;;;;;;;;;;;;;;;;;;;;;;;;; environment

;;;;;;;;;;;;;;;; initial environment ;;;;;;;;;;;;;;;;
  ;; init-env : () -> environment

  ;; (init-env) builds an environment in which i is bound to the
  ;; expressed value 1, v is bound to the expressed value 5, and x is
;; bound to the expressed value 10.

(define init-env
  (lambda ()
    (extend-env1
     'i (newref (num-val 1))
     (extend-env1
      'v (newref (num-val 5))
      (extend-env1
       'x (newref (num-val 10))
       (empty-env))))))

(define extend-env1
  (lambda (id val env)
    (extend-env (list id) (list val) env)))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;
(define apply-env
  (lambda (env search-sym)
    (cases environment env
	   (empty-env ()
		      (eopl:error 'apply-env "No binding for ~s" search-sym))
	   (extend-env (bvars bvals saved-env)
		       (cond
			((location search-sym bvars)
			 => (lambda (n)
			      (list-ref bvals n)))
			(else
			 (apply-env saved-env search-sym))))
	   (extend-env-rec** (p-names b-varss p-bodies saved-env)
			     (cond
			      ((location search-sym p-names)
			       => (lambda (n)
				    (newref
				     (proc-val
				      (procedure
				       (list-ref b-varss n)
				       (list-ref p-bodies n)
				       env)))))
			      (else (apply-env saved-env search-sym))))
	   (extend-env-with-self-and-super (self super-name saved-env)
					   (case search-sym
					     ((%self) self)
					     ((%super) super-name)
					     (else (apply-env saved-env search-sym)))))))

;; new stuff
(define lookup-self-and-super
  (lambda (env search-sym)
     (cases environment env
       (empty-env () #f)
       (extend-env-with-self-and-super (self super-name saved-env)
                                       (case search-sym
                                         [(%self) self]
                                         [(%super) super-name]
                                         [else (lookup-self-and-super saved-env search-sym)]))
       (extend-env (bvars bvals saved-env)
                   (lookup-self-and-super saved-env search-sym))
       (extend-env-rec** (p-names b-varss p-bodies saved-env)
                         (lookup-self-and-super saved-env search-sym)))))
       

;; location : Sym * Listof(Sym) -> Maybe(Int)
;; (location sym syms) returns the location of sym in syms or #f is
;; sym is not in syms.  We can specify this as follows:
;; if (memv sym syms)
;;   then (list-ref syms (location sym syms)) = sym
;;   else (location sym syms) = #f
(define location
  (lambda (sym syms)
    (cond
     ((null? syms) #f)
     ((eqv? sym (car syms)) 0)
     ((location sym (cdr syms))
      => (lambda (n)
	   (+ n 1)))
     (else #f))))

;;;;;;;;;;;;;;;;;;;;;;; data-structure
;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean, a procval, or a
;;; reference.

  (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?))
    (proc-val
      (proc proc?))
    (ref-val
      (ref reference?))
    (obj-val
      (obj object?))
    (list-val
      (lst (list-of expval?)))
    )

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

  ;; not used.  Nor is expval->obj or expval->list, so we haven't
  ;; written them.
  (define expval->ref
    (lambda (v)
      (cases expval v
	(ref-val (ref) ref)
	(else (expval-extractor-error 'reference v)))))

  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

  (define-datatype proc proc?
    (procedure
      (vars (list-of symbol?))
      (body expression?)
      (env environment?)))

  (define-datatype environment environment?
    (empty-env)
    (extend-env
      (bvars (list-of symbol?))
      (bvals (list-of reference?))
      (saved-env environment?))
    (extend-env-rec**
      (proc-names (list-of symbol?))
      (b-varss (list-of (list-of symbol?)))
      (proc-bodies (list-of expression?))
      (saved-env environment?))
    (extend-env-with-self-and-super
      (self object?)
      (super-name symbol?)
      (saved-env environment?)))

;; env->list : Env -> List
;; used for pretty-printing and debugging
(define env->list
  (lambda (env)
    (cases environment env
      (empty-env () '())
      (extend-env (sym val saved-env)
                  (cons
                   (list sym val)
                   (env->list saved-env)))
      (extend-env-rec** (p-names b-varss p-bodies saved-env)
                        (cons
                         (list 'letrec p-names '...)
                         (env->list saved-env)))
      (extend-env-with-self-and-super (self super-name saved-env)
                                      (cons
                                       (list 'self self 'super super-name)
                                       (env->list saved-env))))))

;; expval->printable : ExpVal -> List
;; returns a value like its argument, except procedures get cleaned
;; up with env->list
(define expval->printable
  (lambda (val)
    (cases expval val
      (proc-val (p)
                (cases proc p
                  (procedure (var body saved-env)
                             (list 'procedure var '... (env->list saved-env)))))
      (else val))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;; store
;;;;;;;;;;;;;;;; references and the store ;;;;;;;;;;;;;;;;

  ;;; world's dumbest model of the store:  the store is a list and a
  ;;; reference is number which denotes a position in the list.

  ;; the-store: a Scheme variable containing the current state of the
  ;; store.  Initially set to a dummy variable.
(define the-store 'uninitialized)

;; empty-store : () -> Sto
(define empty-store
  (lambda () '()))

;; initialize-store! : () -> Sto
;; usage: (initialize-store!) sets the-store to the empty-store
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

;; get-store : () -> Sto
;; This is obsolete.  Replaced by get-store-as-list below
(define get-store
  (lambda () the-store))

;; reference? : SchemeVal -> Bool
(define reference?
  (lambda (v)
    (integer? v)))

;; newref : ExpVal -> Ref
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store
            (append the-store (list val)))
      next-ref)))

;; deref : Ref -> ExpVal
(define deref
  (lambda (ref)
    (list-ref the-store ref)))

;; setref! : Ref * ExpVal -> Unspecified
(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                ;; returns a list like store1, except that position ref1
                ;; contains val.
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     (report-invalid-reference ref the-store))
                    ((zero? ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref the-store)))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))



(run
"
class a extends object
 * public c
 public initialize () set c = 10

let b = new a ()
in 5
")

(run
"
class a extends object
 * protect c
 public initialize () set c = 10
 public m1 () fieldref self c

let b = new a ()
in send b m1()
")
(run
"
class a extends object
 * private c
 public initialize () set c = 10
 public m1 () fieldref self c

let b = new a ()
in send b m1()
")




