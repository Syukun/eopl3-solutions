#lang eopl
;; 扩展代码，允许接口的继承，看起来好复杂的样子。

;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;
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
     ("proc" "(" (separated-list identifier ":" type ",") ")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    (expression
     ("letrec"
      (arbno type identifier "(" (separated-list identifier ":" type ",") ")"
	     "=" expression)
      "in" expression)
     letrec-exp)

    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)

    (expression
     ("set" identifier "=" expression)
     assign-exp)

    ;; non-empty lists for typechecked version
    (expression
     ("list" "(" expression (arbno "," expression) ")" )
     list-exp)

    ;; new productions for oop
    (class-decl
     ("class" identifier
      "extends" identifier
      (arbno "implements" identifier)
      (arbno "field" type identifier)
      (arbno method-decl)
      )
     a-class-decl)

    (method-decl
     ("method" type identifier
      "("  (separated-list identifier  ":" type ",") ")" ; method formals
      expression
      )
     a-method-decl)

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

    ;; new productions for typed-oo

    (class-decl
     ("interface" identifier
                  (arbno "extends" identifier)
                  (arbno abstract-method-decl))
     an-interface-decl)


    (abstract-method-decl
     ("method" type identifier
      "("  (separated-list identifier ":" type ",") ")" )
     an-abstract-method-decl)

    (expression
     ("cast" expression identifier)
     cast-exp)

    (expression
     ("instanceof" expression identifier)
     instanceof-exp)

    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("void") void-type)
    (type
     ("(" (separated-list type "*") "->" type ")")
     proc-type)
    (type
     ("listof" type)
     list-type)

    (type (identifier) class-type) ;; new for typed oo


    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; syntactic operations on types ;;;;;;;;;;;;;;;;

(define type->class-name
  (lambda (ty)
    (cases type ty
	   (class-type (name) name)
	   (else (eopl:error 'type->class-name
			"Not a class type: ~s"
			ty)))))

(define class-type?
  (lambda (ty)
    (cases type ty
	   (class-type (name) #t)
	   (else #f))))

(define type-to-external-form
  (lambda (ty)
    (cases type ty
	   (int-type () 'int)
	   (bool-type () 'bool)
	   (void-type () 'void)
	   (class-type (name) name)
	   (list-type (ty) (list 'listof (type-to-external-form ty)))
	   (proc-type (arg-types result-type)
		      (append
		       (formal-types-to-external-form arg-types)
		       '(->)
		       (list (type-to-external-form result-type)))))))

(define formal-types-to-external-form
  (lambda (types)
    (if (null? types)
        '()
        (if (null? (cdr types))
	    (list (type-to-external-form (car types)))
	    (cons
	     (type-to-external-form (car types))
	     (cons '*
		   (formal-types-to-external-form (cdr types))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; checker ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
           (a-program (class-decls exp1)
                      (initialize-static-class-env! class-decls)
                      (for-each check-class-decl! class-decls)
                      (type-of exp1 (init-tenv))))))

;; type-of : Exp -> Tenv
(define type-of
  (lambda (exp tenv)
    (cases expression exp

           (const-exp (num) (int-type))

           (var-exp (var) (apply-tenv tenv var))

           (diff-exp (exp1 exp2)
                     (let ((type1 (type-of exp1 tenv))
                           (type2 (type-of exp2 tenv)))
                       (check-equal-type! type1 (int-type) exp1)
                       (check-equal-type! type2 (int-type) exp2)
                       (int-type)))

           (sum-exp (exp1 exp2)
                    (let ((type1 (type-of exp1 tenv))
                          (type2 (type-of exp2 tenv)))
                      (check-equal-type! type1 (int-type) exp1)
                      (check-equal-type! type2 (int-type) exp2)
                      (int-type)))

           (zero?-exp (exp1)
                      (let ((type1 (type-of exp1 tenv)))
                        (check-equal-type! type1 (int-type) exp1)
                        (bool-type)))

           (if-exp (test-exp true-exp false-exp)
                   (let
                       ((test-type (type-of test-exp tenv))
                        (true-type (type-of true-exp tenv))
                        (false-type (type-of false-exp tenv)))
                     ;; these tests either succeed or raise an error
                     (check-equal-type! test-type (bool-type) test-exp)
                     (check-equal-type! true-type false-type exp)
                     true-type))

           (let-exp (ids rands body)
                    (let ((new-tenv
                           (extend-tenv
                            ids
                            (types-of-exps rands tenv)
                            tenv)))
                      (type-of body new-tenv)))

           (proc-exp (bvars bvar-types body)
                     (let ((result-type
                            (type-of body
                                     (extend-tenv bvars bvar-types tenv))))
                       (proc-type bvar-types result-type)))

           (call-exp (rator rands)
                     (let ((rator-type (type-of rator tenv))
                           (rand-types  (types-of-exps rands tenv)))
                       (type-of-call rator-type rand-types rands exp)))

           (letrec-exp (proc-result-types proc-names
                                          bvarss bvar-typess proc-bodies
                                          letrec-body)
                       (let ((tenv-for-letrec-body
                              (extend-tenv
                               proc-names
                               (map proc-type bvar-typess proc-result-types)
                               tenv)))
                         (for-each
                          (lambda (proc-result-type bvar-types bvars proc-body)
                            (let ((proc-body-type
                                   (type-of proc-body
                                            (extend-tenv
                                             bvars
                                             bvar-types
                                             tenv-for-letrec-body)))) ;; !!
                              (check-equal-type!
                               proc-body-type proc-result-type proc-body)))
                          proc-result-types bvar-typess bvarss proc-bodies)
                         (type-of letrec-body tenv-for-letrec-body)))

           (begin-exp (exp1 exps)
                      (letrec
                          ((type-of-begins
                            (lambda (e1 es)
                              (let ((v1 (type-of e1 tenv)))
                                (if (null? es)
                                    v1
                                    (type-of-begins (car es) (cdr es)))))))
                        (type-of-begins exp1 exps)))

           (assign-exp (id rhs)
                       (check-is-subtype!
                        (type-of rhs tenv)
                        (apply-tenv tenv id)
                        exp)
                       (void-type))

           (list-exp (exp1 exps)
                     (let ((type-of-car (type-of exp1 tenv)))
                       (for-each
                        (lambda (exp)
                          (check-equal-type!
                           (type-of exp tenv)
                           type-of-car
                           exp))
                        exps)
                       (list-type type-of-car)))

           ;; object stuff begins here
           (new-object-exp (class-name rands) ;; 类的名称以及参数
                           (let ((arg-types (types-of-exps rands tenv)) ;; 求出参数的类型
                                 (c (lookup-static-class class-name))) ;; 找到这个类
                             (cases static-class c
                                    (an-interface (method-tenv) ;; 如果是接口,怎么能new一个接口呢?你开玩笑呢?
                                                  (report-cant-instantiate-interface class-name))
                                    (a-static-class (super-name i-names ;; 父类的名称,接口的名字
                                                                field-names field-types method-tenv)
                                                    ;; check the call to initialize
                                                    (type-of-call
                                                     (find-method-type
                                                      class-name
                                                      'initialize)
                                                     arg-types
                                                     rands
                                                     exp)
                                                    ;; and return the class name as a type
                                                    (class-type class-name)))))

           (self-exp ()
                     (apply-tenv tenv '%self))

           (method-call-exp (obj-exp method-name rands) ;; 调用类的这个方法
                            (if (eqv? 'initialize method-name)
                                (eopl:error "You can't invoke initialize method!\n")
                                (let ((arg-types (types-of-exps rands tenv)) ;; 参数的类型
                                      (obj-type (type-of obj-exp tenv))) ;; obj的类型
                                  (type-of-call
                                   (find-method-type ;; 先找到对应的方法么?
                                    (type->class-name obj-type)
                                    method-name)
                                   arg-types ;; 比对参数的类型
                                   rands
                                   exp)))) ;; 如果通过了的话,那么就算出exp的类型
                            
           (super-call-exp (method-name rands)
                           (let ((arg-types (types-of-exps rands tenv))
                                 (obj-type (apply-tenv tenv '%self)))
                             (type-of-call
                              (find-method-type
                               (apply-tenv tenv '%super)
                               method-name)
                              arg-types
                              rands
                              exp)))

           ;; this matches interp.scm:  interp.scm calls
           ;; object->class-name, which fails on a non-object, so we need
           ;; to make sure that obj-type is in fact a class type.
           ;; interp.scm calls is-subclass?, which never raises an error,
           ;; so we don't need to do anything with class-name here.
      ; 这道题目其实也非常简单,只要求class-name是obj-type的子类或者相同的类型即可
      (cast-exp (exp class-name) ;; 这玩意是转型么?
                (let ((obj-type (type-of exp tenv)))
                  (if (is-static-class class-name) 
                      (if (class-type? obj-type) ;; 要求 exp计算出来的东西是一个object
                          (let ([obj-class-name (type->class-name obj-type)])
                            (if (statically-is-subclass? obj-class-name class-name) ;; 判断class-name指代的类是exp指代的类的父类吗=>name2是name1的父类吗
                                (class-type class-name)
                                (eopl:error "~a is not the subclass of ~a!\n" obj-class-name class-name)))
                          (report-bad-type-to-cast obj-type exp))
                      (eopl:error "cast expression : ~a is not a class name!\n" class-name))))

           ;; instanceof in interp.scm behaves the same way as cast:  it
           ;; calls object->class-name on its argument, so we need to
           ;; check that the argument is some kind of object, but we
           ;; don't need to look at class-name at all.

      (instanceof-exp (exp class-name) ;; 我们要修改这里的代码          
                      (let ((obj-type (type-of exp tenv)))
                        (eopl:printf " exp -> ~a\n obj-type -> ~a\n" exp obj-type)
                        (if (is-static-class class-name)
                            (if (class-type? obj-type)
                                (bool-type)
                                (report-bad-type-to-instanceof obj-type exp))
                            (eopl:error "instanceof expression : \n ~a is not a class!\n" class-name))))

      )))

(define is-static-class
  (lambda (name)
    (if (assq name the-static-class-env)
        #t
        #f)))

(define report-cant-instantiate-interface
  (lambda (class-name)
    (eopl:error 'type-of-new-obj-exp
           "Can't instantiate interface ~s"
           class-name)))

(define types-of-exps
  (lambda (rands tenv)
    (map (lambda (exp) (type-of exp tenv)) rands)))

;; type-of-call : Type * Listof(Type) * Listof(Exp) -> Type
(define type-of-call
  (lambda (rator-type rand-types rands exp) ;;
    (cases type rator-type
           (proc-type (arg-types result-type) ;; proc 类型,
                      (if (not (= (length arg-types) (length rand-types))) ;; 首先的话,长度要相等
                          (report-wrong-number-of-arguments arg-types rand-types
                                                            exp) #f)
                      (for-each check-is-subtype! rand-types arg-types rands) ;; 然后实参和形参的类型是否匹配
                      result-type)
           (else
            (report-rator-not-of-proc-type
             (type-to-external-form rator-type)
             exp)))))

(define report-rator-not-of-proc-type
  (lambda (external-form-rator-type exp)
    (eopl:error 'type-of-call
           "rator ~s is not of proc-type ~s"
           exp external-form-rator-type)))

(define report-wrong-number-of-arguments
  (lambda (arg-types rand-types exp)
    (eopl:error 'type-of-call
           "These are not the same: ~s and ~s in ~s"
           (map type-to-external-form arg-types)
           (map type-to-external-form rand-types)
           exp)))

;; check-class-decl! : ClassDecl -> Unspecified
(define check-class-decl! ;; 检查类的定义
  (lambda (c-decl)
    (cases class-decl c-decl
           (an-interface-decl (i-name parents abs-method-decls) ;; 这里是接口的定义,接口的定义一定是通过的嘛。
                              #t)
           (a-class-decl (class-name super-name i-names
                                     field-types field-names method-decls) ;; 这里是类的定义
                         (let ((sc (lookup-static-class class-name))) ;; 先找到对应的类的定义
                           (for-each
                            (lambda (method-decl) ;; 对于每一个方法的定义
                              (check-method-decl! method-decl ;; 检查这些方法
                                                  class-name super-name
                                                  (static-class->field-names sc)
                                                  (static-class->field-types sc)))
                            method-decls))
                         (for-each
                          (lambda (i-name) ;; 然后要做的是,接口必须都要实现才行
                            (check-if-implements! class-name i-name))
                          i-names)
                         ))))

;; check-method-decl! :
;;   MethodDecl * ClassName * ClassName * Listof(FieldName) * \Listof(Type)
;;    -> Unspecified
(define check-method-decl! ;; 用于检查方法定义和实现是否相符合
  (lambda (m-decl self-name s-name f-names f-types) ;; m-decl是一个声明的定义 
    (cases method-decl m-decl
           (a-method-decl (res-type m-name vars var-types body) ;; 一个方法的声明
                          (let ((tenv
                                 (extend-tenv
                                  vars var-types
                                  (extend-tenv-with-self-and-super
                                   (class-type self-name)
                                   s-name ;; 父类的名字
                                   (extend-tenv f-names f-types ;; field names field-types
                                                (init-tenv)))))) ;; 很好,构建了一个新的tenv
                            (let ((body-type (type-of body tenv))) ;; 然后来计算方法的body部分的类型
                              (check-is-subtype! body-type res-type m-decl) ;; 检查声明的和实际计算出的返回值类型是否相等
                              (if (eqv? m-name 'initialize) #t ;; 初始化
                                  (let ((maybe-super-type
                                         (maybe-find-method-type
                                          (static-class->method-tenv
                                           (lookup-static-class s-name))
                                          m-name)))
                                    (if maybe-super-type
                                        (check-is-subtype!
                                         (proc-type var-types res-type) ;; 为什么这个东西要单独拿出来比较呢?
                                         maybe-super-type body)
                                        #t)))))))))

;; check-if-implements! : ClassName * InterfaceName -> Bool
(define check-if-implements! ;; 主要用于检查是否实现了接口
  (lambda (c-name i-name)
    (cases static-class (lookup-static-class i-name) ;; 先找到对应的接口的定义
           (a-static-class (s-name i-names f-names f-types
                                   m-tenv)
                           (report-cant-implement-non-interface
                            c-name i-name))
           (an-interface (method-tenv)
                         (let ((class-method-tenv
                                (static-class->method-tenv
                                 (lookup-static-class c-name)))) ;; 找到类的定义
                           (for-each
                            (lambda (method-binding)
                              (let ((m-name (car method-binding))
                                    (m-type (cadr method-binding)))
                                (let ((c-method-type
                                       (maybe-find-method-type
                                        class-method-tenv
                                        m-name)))
                                  (if c-method-type
                                      (check-is-subtype!
                                       c-method-type m-type c-name)
                                      (report-missing-method
                                       c-name i-name m-name)))))
                            method-tenv))))))

(define report-cant-implement-non-interface
  (lambda (c-name i-name)
    (eopl:error 'check-if-implements
           "class ~s claims to implement non-interface ~s"
           c-name i-name)))

(define report-missing-method
  (lambda (c-name i-name i-m-name)
    (eopl:error 'check-if-implements
           "class ~s claims to implement ~s, missing method ~s"
           c-name i-name i-m-name)))

;;;;;;;;;;;;;;;; types ;;;;;;;;;;;;;;;;

(define check-equal-type!
  (lambda (t1 t2 exp) ;; 检查两个类型是否相等
    (if (equal? t1 t2)
        #t
        (eopl:error 'type-of
               "Types didn't match: ~s != ~s in~%~s"
               (type-to-external-form t1)
               (type-to-external-form t2)
               exp))))

;; check-is-subtype! : Type * Type * Exp -> Unspecified
(define check-is-subtype!
  (lambda (ty1 ty2 exp)
    (if (is-subtype? ty1 ty2)
        #t
        (report-subtype-failure
         (type-to-external-form ty1)
         (type-to-external-form ty2)
         exp))))

(define report-subtype-failure
  (lambda (external-form-ty1 external-form-ty2 exp)
    (eopl:error 'check-is-subtype!
           "~s is not a subtype of ~s in ~%~s"
           external-form-ty1
           external-form-ty2
           exp)))

;; need this for typing cast expressions
;; is-subtype? : Type * Type -> Bool
(define is-subtype? ;; ty1是ty2的子类型吗?
  (lambda (ty1 ty2)
    (cases type ty1
           (class-type (name1)
                       (cases type ty2
                              (class-type (name2)
                                          (statically-is-subclass? name1 name2)) ;; 比较两个类的从属关系
                              (else #f)))
           (proc-type (args1 res1) 
                      (cases type ty2
                             (proc-type (args2 res2)
                                        (and
                                         (every2? is-subtype? args2 args1)
                                         (is-subtype? res1 res2)))
                             (else #f)))
           (else (equal? ty1 ty2)))))

(define andmap
  (lambda (pred lst1 lst2) ;; pred是一个参数好伐。
    (cond
     ((and (null? lst1) (null? lst2)) #t)
     ((or (null? lst1) (null? lst2)) #f) ; or maybe throw error
     ((pred (car lst1) (car lst2))
      (andmap pred (cdr lst1) (cdr lst2)))
     (else #f))))

(define every2? andmap)

;; statically-is-subclass? : ClassName * ClassName -> Bool
(define statically-is-subclass?
  (lambda (name1 name2) ;; name2是name1的父类吗?
    (or
     (eqv? name1 name2)
     (let ((super-name
            (static-class->super-name
             (lookup-static-class name1))))
       (if super-name
           (statically-is-subclass? super-name name2)
           #f))
     (let ((interface-names
            (static-class->interface-names
             (lookup-static-class name1)))) ;; 在name1所指代的类的定义中寻找接口的名字
       (memv name2 interface-names))))) ;; 判定 name2是否在这些接口之中

(define report-bad-type-to-cast
  (lambda (type exp)
    (eopl:error 'bad-type-to-case
           "can't cast non-object; ~s had type ~s"
           exp
           (type-to-external-form type))))

(define report-bad-type-to-instanceof
  (lambda (type exp)
    (eopl:error 'bad-type-to-case
           "can't apply instanceof to non-object; ~s had type ~s"
           exp
           (type-to-external-form type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; environment ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; static classes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;; method type environments ;;;;;;;;;;;;;;;;

;; a method tenv looks like ((method-name type) ...)
;; each method will have a proc-type

  ;;;;;;;;;;;;;;;; static classes ;;;;;;;;;;;;;;;;

(define identifier? symbol?)

(define method-tenv?
  (list-of
   (lambda (p)
     (and
      (pair? p)
      (symbol? (car p))
      (type? (cadr p))))))

(define-datatype static-class static-class?
  (a-static-class
   (super-name (maybe identifier?)) ;; 父类的名字
   (interface-names (list-of identifier?)) ;; 接口的名字
   (field-names (list-of identifier?)) 
   (field-types (list-of type?))
   (method-tenv method-tenv?))
  (an-interface
   (method-tenv method-tenv?)))

;; method-tenv * id -> (maybe type)
(define maybe-find-method-type ;; 找到方法的类型
  (lambda (m-env id)
    (cond
     ((assq id m-env) => cadr)
     (else #f))))

;; class-name * id -> type OR fail
(define find-method-type ;; 找到对应的方法
  (lambda (class-name id)
    (let ((m (maybe-find-method-type
              (static-class->method-tenv (lookup-static-class class-name))
              id)))
      (if m m
          (eopl:error 'find-method
                 "unknown method ~s in class ~s"
                 id class-name)))))

  ;;;;;;;;;;;;;;;; the static class environment ;;;;;;;;;;;;;;;;

;; the-static-class-env will look like ((class-name static-class) ...)

(define the-static-class-env '())

(define is-static-class?
  (lambda (name)
    (assq name the-static-class-env)))

(define lookup-static-class
  (lambda (name)
    (cond
     ((assq name the-static-class-env)
      => (lambda (pair) (cadr pair)))
     (else (eopl:error 'lookup-static-class
                  "Unknown class: ~s" name)))))

(define empty-the-static-class-env!
  (lambda ()
    (set! the-static-class-env '())))

(define add-static-class-binding!
  (lambda (name sc) ;; 名字 以及 sc代表什么含义啊?
    (set! the-static-class-env
          (cons
           (list name sc)
           the-static-class-env))))


  ;;;;;;;;;;;;;;;; class declarations, etc. ;;;;;;;;;;;;;;;;

;; first, pull out all the types and put them in
;; the-static-class-env.

;; initialize-static-class-env! : Listof(ClassDecl) -> Unspecified
(define initialize-static-class-env!
  (lambda (c-decls)
    (empty-the-static-class-env!)
    (add-static-class-binding!
     'object (a-static-class #f '() '() '() '()))
    (for-each add-class-decl-to-static-class-env! c-decls)))

(define append-tenvs
  (lambda (tenvs)
    (if (null? tenvs) '()
        (append (car tenvs) (append-tenvs (cdr tenvs))))))

;; add-class-decl-to-static-class-env! : ClassDecl -> Unspecified
(define add-class-decl-to-static-class-env! ;; 将类型的定义转化成为static class env
  (lambda (c-decl)
    (cases class-decl c-decl
           (an-interface-decl (i-name parents abs-m-decls) ;; 接口的话,要合并啊
                              (let ([parent-tenvs (map (lambda (parent)
                                                         (cases static-class (lookup-static-class parent)
                                                           (an-interface (env) env)
                                                           (else (eopl:error "it is not a interface!"))
                                                           ))
                                                           parents)])
                                (let ([p-tenv (append-tenvs parent-tenvs)]) 
                                  (eopl:printf "parent-tenvs -> ~a\n p-tenv -> ~a\n" parent-tenvs p-tenv)
                                  (let ((m-tenv
                                         (append p-tenv (abs-method-decls->method-tenv abs-m-decls))))
                                    (check-no-dups! (map car m-tenv) i-name) ;; 这里的检查实际上是非常弱的，因为只检查了名字
                                    (add-static-class-binding!
                                     i-name (an-interface m-tenv))))))
           (a-class-decl (c-name s-name i-names
                                 f-types f-names m-decls) ;; 类的定义
                         (let ((i-names
                                (append
                                 (static-class->interface-names
                                  (lookup-static-class s-name)) ;; 取出父类实现了的接口的名字
                                 i-names))
                               (f-names
                                (append-field-names
                                 (static-class->field-names
                                  (lookup-static-class s-name))
                                 f-names)) ;; 取出父类里面有的field-names,和自己有的混合在一起
                               (f-types
                                (append
                                 (static-class->field-types
                                  (lookup-static-class s-name))
                                 f-types)) ;;取出父类中的field的type,和自己的混合在一起
                               (method-tenv
                                (let ((local-method-tenv
                                       (method-decls->method-tenv m-decls)))
                                  (check-no-dups! ;; 应该是检查没有重复吧!
                                   (map car local-method-tenv) c-name)
                                  (merge-method-tenvs ;; 合并tenv
                                   (static-class->method-tenv
                                    (lookup-static-class s-name))
                                   local-method-tenv))))
                           (check-no-dups! i-names c-name)
                           (check-no-dups! f-names c-name)
                           (check-for-initialize! method-tenv c-name)
                           (add-static-class-binding! c-name
                                                      (a-static-class
                                                       s-name i-names f-names f-types method-tenv)))))))

(define abs-method-decls->method-tenv
  (lambda (abs-m-decls)
    (map
     (lambda (abs-m-decl)
       (cases abstract-method-decl abs-m-decl ;; 这里是所谓的抽象方法的定义吗?
              (an-abstract-method-decl (result-type m-name arg-ids arg-types)
                                       (list m-name (proc-type arg-types result-type)))))
     abs-m-decls)))


(define method-decls->method-tenv
  (lambda (m-decls)
    (map
     (lambda (m-decl)
       (cases method-decl m-decl
              (a-method-decl (result-type m-name arg-ids arg-types body) ;; 好吧,其实这个玩意非常的简陋,是吧!
                             (list m-name (proc-type arg-types result-type)))))
     m-decls)))

;; append-field-names :  Listof(FieldName) * Listof(FieldName)
;;                       -> Listof(FieldName)
;; Page: 344
;; like append, except that any super-field that is shadowed by a
;; new-field is replaced by a gensym
(define append-field-names
  (lambda (super-fields new-fields)
    (cond
     ((null? super-fields) new-fields)
     (else
      (cons
       (if (memq (car super-fields) new-fields)
           (fresh-identifier (car super-fields))
           (car super-fields))
       (append-field-names
        (cdr super-fields) new-fields))))))

;; new methods override old ones.
(define merge-method-tenvs ;; 新的方法覆盖了旧的方法
  (lambda (super-tenv new-tenv)
    (append new-tenv super-tenv)))

(define check-for-initialize! ;; 这个东西是要检查是否存在initialize方法。
  (lambda (method-tenv class-name)
    (if (not (maybe-find-method-type method-tenv 'initialize))
        (eopl:error 'check-for-initialize!
               "no initialize method in class ~s"
               class-name) #f)))


;;;;;;;;;;;;;;;; selectors ;;;;;;;;;;;;;;;;

(define static-class->super-name ;; 获得父类的名字
  (lambda (sc)
    (cases static-class sc
           (a-static-class (super-name interface-names
                                       field-names field-types method-types)
                           super-name)
           (else (report-static-class-extractor-error 'super-name sc)))))


(define static-class->interface-names
  (lambda (sc)
    (cases static-class sc
           (a-static-class (super-name interface-names
                                       field-names field-types method-types)
                           interface-names) ;; 可能存在多个接口吧!
           (else (report-static-class-extractor-error 'interface-names sc)))))


(define static-class->field-names
  (lambda (sc)
    (cases static-class sc
           (a-static-class (super-name interface-names
                                       field-names field-types method-types)
                           field-names)
           (else (report-static-class-extractor-error 'field-names sc)))))

(define static-class->field-types
  (lambda (sc)
    (cases static-class sc
           (a-static-class (super-name interface-names
                                       field-names field-types method-types)
                           field-types)
           (else (report-static-class-extractor-error 'field-types sc)))))

(define static-class->method-tenv
  (lambda (sc)
    (cases static-class sc
           (a-static-class (super-name interface-names
                                       field-names field-types method-tenv)
                           method-tenv)
           (an-interface (method-tenv) method-tenv))))

(define report-static-class-extractor-error
  (lambda (sym sc)
    (eopl:error 'static-class-extractors
           "can't take ~s of interface ~s"
           sym sc)))

;; Listof(SchemeVal) * SchemeVal -> Unspecified
(define check-no-dups! ;; 这个函数主要是干什么的呢?
  (lambda (lst blamee)
    (let loop ((rest lst))
      (cond
       ((null? rest) #t)
       ((memv (car rest) (cdr rest)) ;; 检查没有出现重复
        (eopl:error 'check-no-dups! "duplicate found among ~s in class ~s" lst
               blamee))
       (else (loop (cdr rest)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; classes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;; objects ;;;;;;;;;;;;;;;;

;; an object consists of a symbol denoting its class, and a list of
;; references representing the managed storage for the all the
;; fields.

(define-datatype object object?
  (an-object
   (class-name symbol?)
   (fields (list-of reference?))))

(define new-object
  (lambda (class-name)
    (an-object
     class-name
     (map
      (lambda (field-id)
        (newref (list 'uninitialized-field field-id)))
      (class->field-names (lookup-class class-name))))))

;;;;;;;;;;;;;;;; methods and method environments ;;;;;;;;;;;;;;;;

(define-datatype method method?
  (a-method
   (vars (list-of symbol?))
   (body expression?)
   (super-name symbol?)
   (field-names (list-of symbol?))))

;;;;;;;;;;;;;;;; method environments ;;;;;;;;;;;;;;;;

;; a method environment looks like ((method-name method) ...)

(define method-environment?
  (list-of
   (lambda (p)
     (and
      (pair? p)
      (symbol? (car p))
      (method? (cadr p))))))

;; find-method : Sym * Sym -> Method
(define find-method
  (lambda (c-name name)
    (let ((m-env (class->method-env (lookup-class c-name))))
      (let ((maybe-pair (assq name m-env)))
        (if (pair? maybe-pair) (cadr maybe-pair)
            (report-method-not-found name))))))

(define report-method-not-found
  (lambda (name)
    (eopl:error 'find-method "unknown method ~s" name)))

;; merge-method-envs : MethodEnv * MethodEnv -> MethodEnv
;; Page: 345
(define merge-method-envs
  (lambda (super-m-env new-m-env)
    (append new-m-env super-m-env)))

;; method-decls->method-env :
;; Listof(MethodDecl) * ClassName * Listof(FieldName) -> MethodEnv
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (map
     (lambda (m-decl)
       (cases method-decl m-decl
              (a-method-decl (result-type method-name vars var-types body)
                             (list method-name
                                   (a-method vars body super-name field-names)))))
     m-decls)))

;;;;;;;;;;;;;;;; classes ;;;;;;;;;;;;;;;;

(define-datatype class class?
  (a-class
   (super-name (maybe symbol?))
   (field-names (list-of symbol?))
   (method-env method-environment?)))

;;;;;;;;;;;;;;;; class environments ;;;;;;;;;;;;;;;;

;; the-class-env will look like ((class-name class) ...)

;; the-class-env : ClassEnv
;; Page: 343
(define the-class-env '())

;; add-to-class-env! : ClassName * Class -> Unspecified
;; Page: 343
(define add-to-class-env!
  (lambda (class-name class)
    (set! the-class-env
          (cons
           (list class-name class)
           the-class-env))))

;; lookup-class : ClassName -> Class
(define lookup-class
  (lambda (name)
    (let ((maybe-pair (assq name the-class-env)))
      (if maybe-pair (cadr maybe-pair)
          (report-unknown-class name)))))

(define report-unknown-class
  (lambda (name)
    (eopl:error 'lookup-class "Unknown class ~s" name)))

;; constructing classes

;; initialize-class-env! : Listof(ClassDecl) -> Unspecified
;; Page: 344
(define initialize-class-env!
  (lambda (c-decls)
    (set! the-class-env
          (list
           (list 'object (a-class #f '() '()))))
    (for-each initialize-class-decl! c-decls)))

'(define initialize-class-env!
   (lambda (c-decls)
     (set! the-class-env
           (list
            (list 'object (a-class #f '() '()))))
     (for-each initialize-class-decl! c-decls)))

;; initialize-class-decl! : ClassDecl -> Unspecified
(define initialize-class-decl!
  (lambda (c-decl)
    (cases class-decl c-decl
           ;; interfaces don't affect runtime
           (an-interface-decl (interface-name parents method-decls) '())
           (a-class-decl (class-name super-name interface-names field-types field-names method-decls)
                         (let ((field-names
                                (append-field-names
                                 (class->field-names (lookup-class super-name))
                                 field-names)))
                           (add-to-class-env!
                            class-name
                            (a-class
                             super-name
                             field-names
                             (merge-method-envs
                              (class->method-env (lookup-class super-name))
                              (method-decls->method-env
                               method-decls super-name field-names)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;; selectors ;;;;;;;;;;;;;;;;

(define class->super-name
  (lambda (c-struct)
    (cases class c-struct
           (a-class (super-name  field-names method-env)
                    super-name))))

(define class->field-names
  (lambda (c-struct)
    (cases class c-struct
           (a-class (super-name field-names method-env)
                    field-names))))

(define class->method-env
  (lambda (c-struct)
    (cases class c-struct
           (a-class (super-name field-names method-env)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; store ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define instrument-newref (make-parameter #f))

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
      (if (instrument-newref)
          (eopl:printf
           "newref: allocating location ~s with initial contents ~s~%"
           next-ref val) #f)
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


;;;;;;;;;;;;;;;; type environments ;;;;;;;;;;;;;;;;

(define-datatype type-environment type-environment?
  (empty-tenv)
  (extend-tenv
   (syms (list-of symbol?))
   (vals (list-of type?))
   (tenv type-environment?))
  (extend-tenv-with-self-and-super
   (self type?)
   (super-name symbol?)
   (saved-env type-environment?)))

(define init-tenv
  (lambda ()
    (extend-tenv
     '(i v x)
     (list (int-type) (int-type) (int-type))
     (empty-tenv))))

(define apply-tenv
  (lambda (env search-sym)
    (cases type-environment env
           (empty-tenv ()
                       (eopl:error 'apply-tenv "No type found for ~s" search-sym))
           (extend-tenv (bvars types saved-env)
                        (cond
                         ((location search-sym bvars)
                          => (lambda (n) (list-ref types n)))
                         (else
                          (apply-tenv saved-env search-sym))))
           (extend-tenv-with-self-and-super (self-name super-name saved-env)
                                            (case search-sym
                                              ((%self) self-name)
                                              ((%super) super-name)
                                              (else (apply-tenv saved-env search-sym)))))))


(define ck
  (lambda (string)
    (type-of-program (scan&parse string))))

(ck
 "
interface m1
 method int  a()


interface m2 extends m1
 method int b()

interface m4
 method bool c()

interface m3 extends m1 extends m4
 method int d()

class k extends object implements m3
 method int initialize () 1
 method int a () 2
 method bool c () zero?(0)
 method int d () 4

1
")


(ck "interface sum_iface
          method int sum()

        interface sub_iface
          method int sub()

        interface operator extends sum_iface extends sub_iface
          method int is-zero()

        class number extends object
           implements operator
           field int value
         method void initialize(v : int)
             begin
                set value = v
             end
         method int sum()  +(value, value)
         method int sub()  -(value, value)
         method int is-zero() if zero?(value) then 1 else 0

       let obj = new number(1) in
          list(send obj sum(),
               send obj sub(),
               send obj is-zero())")

;; 感觉的话，还有很多需要考虑的地方，比如说，如果接口的method重名咋办？
;; 当然，这里自然不会考虑。











