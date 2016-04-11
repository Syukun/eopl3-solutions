#lang eopl
;; extend the inference to handle multiple let declarations, multiargument procedures, multiple letrec declaration.

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
     ("let" (arbno identifier "=" expression )"in" expression) ;; 要支持多个let声明
     let-exp)

    (expression
     ("proc" "(" (separated-list identifier ":" optional-type ",")")" expression)
     proc-exp)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    ;; 多重letrec，好吧！
    (expression
     ("letrec"
      (separated-list optional-type identifier "(" (separated-list identifier ":" optional-type ",") ")"
      "=" expression ",")"in" expression)
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
     ("(" (arbno type) "->" type ")")
     proc-type) ;; 这里变成了很有趣的东西

    (type
     ("%tvar-type" number)
     tvar-type)

     ;; pair-exp
    (expression
     ("newpair" "(" expression "," expression ")") pair-exp)
    
    (type
     ("pairof" type type)
     pairof-type)

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
      (pairof-type (lty rty) ;; 在这边执行一个替换
                   (pairof-type
                    (apply-one-subst lty tvar ty1)
                    (apply-one-subst rty tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))

;; apply-subst-to-type : Type * Subst -> Type
;; 好吧,这个式子也是非常漂亮的一个式子
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2) ;; 好吧，这里要开始弄了
                 (letrec
                     ([helper (lambda (types subst acc)
                                (if (null? types) acc
                                    (helper (cdr types) subst
                                            (append acc (list (apply-subst-to-type (car types) subst))))))])
                   (proc-type
                    (helper t1 subst '())
                    (apply-subst-to-type t2 subst))))
      (pairof-type (lty rty)
                   (pairof-type
                    (apply-subst-to-type lty subst)
                    (apply-subst-to-type rty subst)))
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
         ;; 好吧，差错应该出现在这里
         (letrec ([add-arg-to-subst
                (lambda (ft st subst)
                  (if (null? ft) subst
                      (add-arg-to-subst (cdr ft) (cdr st)
                                        (unifier
                                         (car ft) (car st) subst exp))))])
           (let ([subst (add-arg-to-subst
                         (proc-type->arg-type ty1)
                         (proc-type->arg-type ty2)
                       subst)])
             (let ([subst (unifier
                           (proc-type->result-type ty1)
                           (proc-type->result-type ty2)
                           subst exp)])
               subst)))]
        
        ;; new stuff
        [(and (pairof-type? ty1) (pairof-type? ty2))
         (let ([subst (unifier
                       (pairof-type->left-type ty1)
                       (pairof-type->left-type ty2)
                       subst exp)])
           (let ([subst (unifier
                         (pairof-type->right-type ty1)
                         (pairof-type->right-type ty2)
                         subst exp)])
             subst))]
        [else (report-unification-failure ty1 ty2 exp)]))))
;; helper function
(define pairof-type->left-type
  (lambda (a-pair)
    (cases type a-pair
      (pairof-type (lty rty) lty)
      (else (eopl:error "~a is not a pair!\n" a-pair)))))

(define pairof-type->right-type
  (lambda (a-pair)
    (cases type a-pair
      (pairof-type (lty rty) rty)
      (else (eopl:error "~a is not a pair!\n" a-pair)))))

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
      (pairof-type (lty rty)
                   (and
                    (no-occurrence? tvar lty)
                    (no-occurrence? tvar rty)))
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

;; 判断一个type是否为pairof-type
(define pairof-type?
  (lambda (ty)
    (cases type ty
           (pairof-type (t1 t2) #t)
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
      (pairof-type (lty rty)
                 (list
                  'pair
                  "("
                  (type-to-external-form lty)
                  ","
                  (type-to-external-form rty)
                  ")"
                  ))
      (tvar-type (serial-number)
                 (string->symbol
                  (string-append
                   "tvar"
                   (number->string serial-number)))))))

(define-datatype answer answer?
  (an-answer
   (ty type?)
   (subst substitution?)))
(define substitution? list?) ;; 好吧,把检查项放得简单了

(define-datatype my-type my-type?
  (demo
   (ty (list-of type?))
   (subst substitution?)))

;; type-of-program : Progarm -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (cases answer (type-of exp1
                                        (init-tenv) (empty-subst))
                   (an-answer (ty subst)
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

      (let-exp (vars exps body)
               (cases my-type (multilet-helper exps tenv subst '())
                 (demo (exps-type subst)
                       (eopl:printf "type-of :\n exps-type -> ~a\n" exps-type)
                       (type-of body
                                (extend-tenv* vars exps-type tenv) subst)))) ;; body 的类型就是let表达式的类型
      

      (proc-exp (vars otypes body)
                (let ([var-types (otypes->types otypes '())]) ;; 这里得到了type list
                  (eopl:printf "type-of :\n var-types -> ~a\n" var-types)
                  (cases answer (type-of body (extend-tenv* vars var-types tenv) subst)
                    (an-answer (body-type subst)
                               (eopl:printf "type-of :\n body-type -> ~a\n" body-type)
                               (an-answer (proc-type var-types body-type) subst)))))
     
      (call-exp (rator rands)
                (let ([result-type (fresh-tvar-type)]) ;; 结果类型
                  (cases answer (type-of rator tenv subst) ;; 操作符的类型
                    (an-answer (rator-type subst)
                               (eopl:printf "type-of - call-exp :\n rator-type -> ~a \n" rator-type)
                               (cases my-type (multilet-helper rands tenv subst '())
                                 (demo (rands-type subst)
                                       (eopl:printf "type-of - call-exp :\n rands-type -> ~a\n result-type -> ~a\n" rands-type result-type)
                                       (let ([subst (unifier rator-type ;; rator-type是一个proc-type
                                                             (proc-type rands-type result-type)
                                                             subst exp)])
                                         (an-answer result-type subst))))))))

      (letrec-exp (p-result-otypes p-names b-vars b-var-obtypes
                                    p-bodies letrec-body)
                  (let ([p-result-types (otypes->types p-result-otypes '())]
                        [p-var-types (map (lambda (ty) (otypes->types ty '())) b-var-obtypes)])
                    (eopl:printf "letrec-exp :\n p-result-types -> ~a\n p-var-types -> ~a\n" p-result-types p-var-types)
                    (let ([proc-types (letrec-helper p-var-types p-result-types)])
                      (let ([tenv-for-letrec-body
                             (extend-tenv* p-names proc-types tenv)])
                        (let ([subst (letrec-addeto-subst b-vars p-var-types
                                                          p-bodies p-result-types
                                                          tenv subst)])
                          (type-of letrec-body tenv-for-letrec-body subst))))))
    
                    
      
                    
      ;; new stuff
      (pair-exp (lexp rexp)
                (cases answer (type-of lexp tenv subst)
                  (an-answer (ltype subst)
                             (cases answer (type-of rexp tenv subst)
                               (an-answer (rtype subst)
                                          (an-answer (pairof-type ltype rtype) subst)))))) 
      (else (eopl:printf "end of the type-of!\n"))
      )))
;; 好吧,又要定义新的函数啦
(define letrec-addeto-subst
  (lambda (b-vars p-var-types p-bodies p-result-types  tenv subst)
    (if (null? p-bodies) subst
        (cases answer (type-of (car p-bodies) (extend-tenv* (car b-vars) (car p-var-types) tenv) subst)
          (an-answer (p-body-type subst)
                     (let ([subst (unifier p-body-type (car p-result-types) subst (car p-bodies))])
                       (letrec-addeto-subst (cdr b-vars) (cdr p-var-types)
                                            (cdr p-bodies) (cdr p-result-types)
                                            tenv subst)))))))
(define letrec-helper
  (lambda (p-var-types p-result-types)
          (if (null? p-var-types) '()
              (cons (proc-type (car p-var-types) (car p-result-types))
                    (letrec-helper (cdr p-var-types) (cdr p-result-types))))))

(define otypes->types
  (lambda (otypes acc)
    (if (null? otypes) acc
        (otypes->types (cdr otypes)
                       (append acc (list
                                    (cases optional-type (car otypes)
                                      (no-type () (fresh-tvar-type))
                                      (a-type (ty) ty))))))))

(define extend-tenv*
  (lambda (vars exps-type tenv)
    (if (null? vars) tenv
        (extend-tenv* (cdr vars) (cdr exps-type)
                      (extend-tenv (car vars) (car exps-type) tenv)))))
(define multilet-helper
  (lambda (exps tenv subst types)
    (if (null? exps) (demo types subst)
        (cases answer (type-of (car exps) tenv subst)
          (an-answer (a-exp-type subst)
                     (multilet-helper (cdr exps) tenv subst (append types (list a-exp-type))))))))

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
(type-of-program (scan&parse "letrec ? f (x : ?) = x, int g (y : ?) = 1 in (g 2)"))
(type-of-program (scan&parse "letrec ? f (x : ?) = x, int g (y : ?) = 1 in (f 2)"))




