#lang eopl
;; 题目的意思是这样的，为什么说，如果ty1是一个未知的类型，那么no-occurrence invariant告诉我们，它未在substitution里面绑定
;; 所谓的未知的类型，就是说ty1是tvar-type，我们还不能推断出它的实际类型。
;; 接下来的事情就很好办了，也就是说不出错的话，ty1是要被一个实际的类型给替换掉的，所以要将ty1 = ty2 加入substitution，当然前提是
;; ty1不在ty2中出现，否则的话，no-occurrence invariant就不能满足了。就是这么简单


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

;; apply-subst-to-type : Type * Subst -> Type
;; 好吧,这个式子也是非常漂亮的一个式子
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type t1 subst)
                  (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
                 (let ([tmp (assoc ty subst)])
                   (if tmp
                       (cdr tmp)
                       ty))))))

;; empty-subst : () -> Subst
(define empty-subst (lambda () '()))

;; extend-subst : Subst * Tvar * Type -> Subst
(define extend-subst
  (lambda (subst tvar ty)
    (cons
     (cons tvar ty)
     (map
      (lambda (p)
        (let ([oldlhs (car p)]
              [oldrhs (cdr p)])
          (cons
           oldlhs
           (apply-one-subst oldrhs tvar ty)))) ;; 将右边的东西中的tvar替换为ty
      subst))))


;; unifier : Type * Type * Subst * Exp -> Subst
(define unifier ;; 这个函数的功能是什么呢？ 我想了一下，这个函数的主要功能是将equations里面的式子添加入substitution里面的
  (lambda (ty1 ty2 subst exp)
    (let ([ty1 (apply-subst-to-type ty1 subst)]
          [ty2 (apply-subst-to-type ty2 subst)])
      (cond
        [(equal? ty1 ty2) subst]
        [(tvar-type? ty1) ;; 运行到了这一步的话，说明ty1和ty2是不相等的。
         (if (no-occurrence? ty1 ty2) ;; 为了维持所谓的no-occurrence invariant,意思是在substitution中绑定的变量不能出现在substitution的右边
             ;; 如果 ty1 = ty2这一条，我们检查出了，ty1 在 ty2 中出现，那么这个不变量肯定不满足
             (extend-subst subst ty1 ty2) ;; 将ty1 = ty2 这条放入substitution中
             (report-no-occurrence-violation ty1 ty2 exp))]
        [(tvar-type? ty2) ;; 同理，这一条这是这么干的
         (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp))]
        [(and (proc-type? ty1) (proc-type? ty2))
         (let ([subst (unifier
                       (proc-type->arg-type ty1)
                       (proc-type->arg-type ty2)
                       subst exp)])
           (let ([subst (unifier
                         (proc-type->result-type ty1)
                         (proc-type->result-type ty2)
                         subst exp)])
             subst))]
        [else (report-unification-failure ty1 ty2 exp)]))))

;; no-occurrence? : Tvar * Type -> Bool
(define no-occurrence? ;; 这个函数的功能是判断ty是否在tvar中出现啦。当然，如果ty不是tvar，肯定不会出现在那里面。
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

;; test code



