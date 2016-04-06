#lang eopl
;; 题目的要求是，我们要修改之前的代码，使得每个tvar-type可以在常数时间内获得相对应的绑定。
;; 其实也不是很难，使用hash表是一个很不错的选择。
;; 但是在这里不支持 hash，很蛋疼的一件事情，要么自己实现hash，我很懒，就不去实现啦。

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
  '((program (expression) a-program)

    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    (expression (identifier) var-exp)

    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("proc" "("  identifier ":" optional-type ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("letrec"
      optional-type identifier "(" identifier ":" optional-type ")"
      "=" expression "in" expression)
     letrec-exp)

    (optional-type
     ("?")
     no-type) ;; 可选的参数

    (optional-type
     (type)
     a-type) ;; a-type是什么玩意

    (type
     ("int")
     int-type)

    (type
     ("bool")
     bool-type)

    (type
     ("(" type "->" type ")")
     proc-type)

    (type
     ("%tvar-type" number)
     tvar-type)

    ))
 ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;; apply-one-subst : Type * Tvar * Type -> Type
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (apply-one-subst arg-type tvar ty1)
                  (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))


;; empty-subst : () -> Subst
(define empty-subst
  (lambda ()
    (set! subst (make-hash null))))

;; unifier : Type * Type * Subst * Exp -> Subst
(define unifier ;; 这个函数的功能是什么呢? 我想了一下,这个函数的主要功能是将equations里面的式子添加入subst里面的
  (lambda (ty1 ty2 exp)
    (let ([ty1 (apply-subst-to-type ty1)]
          [ty2 (apply-subst-to-type ty2)])
      (cond
        [(equal? ty1 ty2) subst]
        [(tvar-type? ty1) ;; 运行到了这一步的话,说明ty1和ty2是不相等的。
         (if (no-occurrence? ty1 ty2) ;; 为了维持所谓的no-occurrence invariant,意思是在subst中绑定的变量不能出现在subst的右边
             ;; 如果 ty1 = ty2这一条,我们检查出了,ty1 在 ty2 中出现,那么这个不变量肯定不满足
             (extend-subst ty1 ty2) ;; 将ty1 = ty2 这条放入subst中
             (report-no-occurrence-violation ty1 ty2 exp))]
        [(tvar-type? ty2) ;; 同理,这一条这是这么干的
         (if (no-occurrence? ty2 ty1)
             (extend-subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp))]
        [(and (proc-type? ty1) (proc-type? ty2))
         (let ([a-subst (unifier (proc-type->arg-type ty1) (proc-type->arg-type ty2) exp)])
           (eopl:printf "a-subst -> ~a\n" a-subst)
           (let ([t-subst (unifier (proc-type->result-type ty1) (proc-type->result-type ty2) exp)])
             (eopl:printf "t-subst -> ~a\n" t-subst)
             t-subst))]
           [else (report-unification-failure ty1 ty2 exp)]))))

;; no-occurrence? : Tvar * Type -> Bool
(define no-occurrence? ;; 这个函数的功能是判断ty是否在tvar中出现啦。当然,如果ty不是tvar,肯定不会出现在那里面。
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type result-type)
                 (and
                  (no-occurrence? tvar arg-type)
                  (no-occurrence? tvar result-type)))
      (tvar-type (serial-number) (not (equal? tvar ty))))))

(define tvar-type?
  (lambda (ty)
    (cases type ty
           (tvar-type (serial-number) #t)
           (else #f))))

(define report-no-occurrence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-no-occurence!
		"Can't unify: type variable ~s occurs in type ~s in expression ~s~%"
		(type-to-external-form ty1)
		(type-to-external-form ty2)
		exp)))

(define proc-type?
  (lambda (ty)
    (cases type ty
           (proc-type (t1 t2) #t)
           (else #f))))

(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
           (proc-type (arg-type result-type) arg-type)
           (else (eopl:error 'proc-type->arg-type
                             "Not a proc type: ~s" ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type ty
           (proc-type (arg-type result-type) result-type)
           (else (eopl:error 'proc-type->result-types
                             "Not a proc type: ~s" ty)))))

(define report-unification-failure
  (lambda (ty1 ty2 exp)
    (eopl:error 'unification-failure
		"Type mismatch: ~s doesn't match ~s in ~s~%"
		(type-to-external-form ty1)
		(type-to-external-form ty2)
		exp)))

;; type-to-external-form : Type -> List
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
           (tvar-type (serial-number)
                      (string->symbol
                       (string-append
                        "tvar"
                        (number->string serial-number)))))))

;; new stuff
(define extend-subst
  (lambda (tvar ty)
    (hash-set! subst tvar ty)
    subst)) ;; 这么做的话会导致没有替换是吧。

;; 其余的工作移步到了apply-subst-to-type里面,也就是说在apply-sub-to-type里面,要将tvar替换为ty
(define apply-subst-to-type
  (lambda (ty)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type t1)
                  (apply-subst-to-type t2)))
     (tvar-type (sn)
                 (let ([tmp (hash-ref subst ty (lambda () (#f)))]) ;; 这样的话，可以在常数时间内找到对应的值
                   (if tmp
                       (apply-subst-to-type (cdr tmp)) ;; 重新另外寻找
                       ty))))))

(define subst 'uinitialized)

;; test code
(empty-subst)

(extend-subst (tvar-type 2) (tvar-type 3))

(unifier (proc-type (tvar-type 1) (bool-type)) (proc-type (int-type) (bool-type)) 'hi)





