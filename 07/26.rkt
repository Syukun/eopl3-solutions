#lang eopl
;; extend the inferencer to handle EXPLICIT-REFS
;; 支持显式地引用类型

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

     ;; 这里是新特性
    (type
     ("listof" type) list-type)
    (expression ("list" "(" expression (arbno "," expression) ")" ) list-exp)
    (expression ("cons" "(" expression "," expression ")" ) cons-exp)
    (expression ("null?" "(" expression ")") null-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    ;; 新加入的语法
    (type
     ("refto" type)
     refto-type) ;; 好吧,这就是所谓的引用类型

    (type
     ("void")
     void-type)

     (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)
     
    (expression
     ("newref" "(" expression ")")
     newref-exp)
    
    (expression
     ("deref" "(" expression ")")
     deref-exp)
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
                 (if (equal? ty0 tvar) ty1 ty0))
      (void-type () (void-type))
      (refto-type (ty)
                  (refto-type (apply-one-subst ty tvar ty1)))
      (list-type (ty)
                 (list-type (apply-one-subst ty tvar ty1)))
      ;(else #f))
    
    )))

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
                       ty)))
      (list-type (ty)
                 (list-type
                  (apply-subst-to-type ty subst)))
      (refto-type (ty)
                  (refto-type
                   (apply-subst-to-type ty subst)))
      
      (else (eopl:printf "apply-subst-to-type!\n"))
      )))

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
(define unifier ;; 这个函数的功能是什么呢? 我想了一下,这个函数的主要功能是将equations里面的式子添加入substitution里面的
  (lambda (ty1 ty2 subst exp)
    (let ([ty1 (apply-subst-to-type ty1 subst)]
          [ty2 (apply-subst-to-type ty2 subst)])
      (cond
        [(equal? ty1 ty2) subst]
        [(tvar-type? ty1) ;; 运行到了这一步的话,说明ty1和ty2是不相等的。
         (if (no-occurrence? ty1 ty2) ;; 为了维持所谓的no-occurrence invariant,意思是在substitution中绑定的变量不能出现在substitution的右边
             ;; 如果 ty1 = ty2这一条,我们检查出了,ty1 在 ty2 中出现,那么这个不变量肯定不满足
             (extend-subst subst ty1 ty2) ;; 将ty1 = ty2 这条放入substitution中
             (report-no-occurrence-violation ty1 ty2 exp))]
        [(tvar-type? ty2) ;; 同理,这一条这是这么干的
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
        [(and (list-type? ty1) (list-type? ty2))
         (let ([subst (unifier
                       (list-type->type ty1)
                       (list-type->type ty2)
                       subst exp)])
           subst)]
        
        [(and (refto-type? ty1) (refto-type? ty2))
         (let ([subst (unifier
                       (refto-type->type ty1)
                       (refto-type->type ty2)
                       subst exp)])
           subst)]
        
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
      (tvar-type (serial-number) (not (equal? tvar ty)))
      (else (eopl:printf "no-occurrence?\n"))
      )))

(define tvar-type?
  (lambda (ty)
    (cases type ty
           (tvar-type (serial-number) #t)
           (else #f))))

(define refto-type?
  (lambda (a-type)
    (cases type a-type
      (refto-type (ty) #t)
      (else #f))))

(define refto-type->type
  (lambda (a-type)
    (cases type a-type
      (refto-type (ty) ty)
      (else (eopl:printf "~a is not a refto-type!\n" a-type)))))
(define list-type?
  (lambda (a-type)
    (cases type a-type
      (list-type (ty) #t)
      (else #f))))

(define list-type->type
  (lambda (a-type)
    (cases type a-type
      (list-type (ty) ty)
      (else (eopl:printf "~a is not a list-type!\n" a-type)))))


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
      (list-type (ty)
                 (list
                  'listof
                  (type-to-external-form ty)
                  ))
      (tvar-type (serial-number)
                 (string->symbol
                  (string-append
                   "tvar"
                   (number->string serial-number))))
      (void-type () 'void)
      (refto-type (ty)
                  (list
                   'refto
                   (type-to-external-form ty)))
      )))

(define-datatype answer answer?
  (an-answer
   (ty type?)
   (subst substitution?)))

(define substitution? list?) ;; 好吧,把检查项放得简单了

;; type-of-program : Progarm -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (cases answer (type-of exp1
                                        (init-tenv) (empty-subst))
                   (an-answer (ty subst)
                              (eopl:printf "type-of-program :\n subst -> ~a\n" subst)
                              (apply-subst-to-type ty subst)))))))

;; type-of : Exp * Tenv * Subst -> Answer
(define type-of
  (lambda (exp tenv subst)
    (cases expression exp
      (const-exp (num) (an-answer (int-type) subst))
      (zero?-exp (exp1)
                 (cases answer (type-of exp1 tenv subst)
                   (an-answer (ty1 subst1)
                              (let ([subst2 (unifier ty1 (int-type) subst1 exp)])
                                (an-answer (bool-type) subst2)))))
      (diff-exp (exp1 exp2)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (ty1 subst1)
                             (let ([subst1 (unifier ty1 (int-type) subst1 exp1)])
                               (cases answer (type-of exp2 tenv subst1)
                                 (an-answer (ty2 subst2)
                                            (let ([subst2 (unifier ty2 (int-type) subst2 exp2)])
                                              (an-answer (int-type) subst2))))))))

      (if-exp (exp1 exp2 exp3)
              (cases answer (type-of exp1 tenv subst)
                (an-answer (ty1 subst)
                           (let ([subst (unifier ty1 (bool-type) subst exp1)])
                             (cases answer (type-of exp2 tenv subst)
                               (an-answer (ty2 subst)
                                          (cases answer (type-of exp3 tenv subst)
                                            (an-answer (ty3 subst)
                                                       (let ([subst (unifier ty2 ty3 subst exp)])
                                                         (an-answer ty2 subst))))))))))
      (var-exp (var)
               (an-answer (apply-tenv tenv var) subst))

      (let-exp (var exp1 body)
               (cases answer (type-of exp1 tenv subst)
                 (an-answer (exp1-type subst)
                            (type-of body
                                     (extend-tenv var exp1-type tenv) ;; body 的类型就是let表达式的类型
                                     subst))))

      (proc-exp (var otype body)
                (let ([var-type (otype->type otype)])
                  (cases answer (type-of body (extend-tenv var var-type tenv) subst)
                    (an-answer (body-type subst)
                              (an-answer (proc-type var-type body-type) subst)))))

      (call-exp (rator rand)
                (let ([result-type (fresh-tvar-type)]) ;; 结果类型
                  (cases answer (type-of rator tenv subst) ;; 操作符的类型
                    (an-answer (rator-type subst)
                               (cases answer (type-of rand tenv subst) ;; 操作数的类型
                                 (an-answer (rand-type subst)
                                            (let ([subst (unifier rator-type ;; rator-type是一个proc-type
                                                                  (proc-type rand-type result-type)
                                                                  subst exp)])
                                              (an-answer result-type subst))))))))
      (list-exp (exp1 exps)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (exp1-type subst)
                             (let ([subst (add-exp-type-to-subst exps exp1-type tenv subst)])
                               (an-answer (list-type exp1-type) subst)))))
      (cons-exp (lexp rexp)
                (cases answer (type-of lexp tenv subst)
                  (an-answer (lexp-type subst)
                             (cases answer (type-of rexp tenv subst)
                               (an-answer (rexp-type subst)
                                          (let ([subst (unifier lexp-type rexp-type subst rexp)])
                                            (an-answer (list-type lexp-type) subst)))))))
      (null-exp (exp)
                 (let ([some-type (fresh-tvar-type)])
                   (cases answer (type-of exp tenv subst)
                     (an-answer (exp-type subst)
                                (let ([subst (unifier (list-type some-type) exp-type subst exp)])
                                  (an-answer (bool-type) subst))))))
      (emptylist-exp ()
                     (let ([some-type (fresh-tvar-type)])
                       (an-answer some-type subst)))
      (newref-exp (exp)
                  (cases answer (type-of exp tenv subst)
                    (an-answer (exp-type subst)
                               (an-answer (refto-type exp-type) subst))))
      (deref-exp (exp) ;; 解引用
                 (let ([some-type (fresh-tvar-type)])
                   (cases answer (type-of exp tenv subst)
                     (an-answer (exp-type subst)
                              (let ([subst (unifier exp-type (refto-type some-type) subst exp)])
                                (an-answer some-type subst))))))
      (car-exp (exp)
               (let ([some-type (fresh-tvar-type)])
                 (cases answer (type-of exp tenv subst)
                   (an-answer (exp-type subst)
                              (let ([subst (unifier exp-type (list-type some-type) subst exp)])
                                (an-answer some-type subst))))))
      (cdr-exp (exp)
               (let ([some-type (fresh-tvar-type)])
                 (cases answer (type-of exp tenv subst)
                   (an-answer (exp-type subst)
                              (let ([subst (unifier exp-type (list-type some-type) subst exp)])
                                (an-answer (list-type some-type) subst))))))

      (letrec-exp (p-result-otype p-name b-var b-var-otype
                                  p-body letrec-body)
                  (let ([p-result-type (otype->type p-result-otype)]
                        [p-var-type (otype->type b-var-otype)])
                    (let ([tenv-for-letrec-body
                           (extend-tenv p-name
                                        (proc-type p-var-type p-result-type)
                                        tenv)])
                      (cases answer (type-of p-body
                                             (extend-tenv b-var p-var-type
                                                          tenv-for-letrec-body))
                        (an-answer (p-body-type subst)
                                   (let ([subst (unifier p-body-type p-result-type
                                                         subst p-body)])
                                     (type-of letrec-body
                                              tenv-for-letrec-body
                                              subst)))))))
      (setref-exp (exp1 exp2)
                  (let ([some-type (fresh-tvar-type)])
                    (cases answer (type-of exp1 tenv subst)
                      (an-answer (exp1-type subst)
                                 (cases answer (type-of exp2 tenv subst)
                                   (an-answer (exp2-type subst)
                                              (let ([subst (unifier exp1-type (refto-type some-type) subst exp)])
                                                (let ([subst (unifier some-type exp2-type subst exp)])
                                                  (an-answer (int-type) subst)))))))))
      ;(else (eopl:printf "end of the type-of!\n"))
      )))
(define add-exp-type-to-subst
  (lambda (exps ty tenv subst)
    (if (null? exps) subst
        (cases answer (type-of (car exps) tenv subst)
          (an-answer (exp-type subst)
                     (let ([subst (unifier exp-type ty subst (car exps))])
                       (add-exp-type-to-subst (cdr exps) ty tenv subst)))))))

(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extended-tenv-record
   (sym symbol?)
   (type type?)
   (tenv type-environment?)))

(define empty-tenv empty-tenv-record)
(define extend-tenv extended-tenv-record)
(define apply-tenv
  (lambda (tenv sym)
    (cases type-environment tenv
	   (empty-tenv-record ()
			      (eopl:error 'apply-tenv "Unbound variable ~s" sym))
	   (extended-tenv-record (sym1 val1 old-env)
				 (if (eqv? sym sym1)
				     val1
				     (apply-tenv old-env sym))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'x (int-type)
		 (extend-tenv 'v (int-type)
			      (extend-tenv 'i (int-type)
					   (empty-tenv))))))

;; fresh-tvar-type : () -> Type
(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))

;; otype->type : OptionalType -> Type
(define otype->type
  (lambda (otype)
    (cases optional-type otype
	   (no-type () (fresh-tvar-type))
	   (a-type (ty) ty))))
      

;; test code
(type-of-program (scan&parse "let f = newref (3) in deref (f)"))
(type-of-program (scan&parse "setref (newref(1), 3)"))


