#lang eopl
;; extend the checker to handle EXPLICIT-REFS
;; 好吧，又来挖坑了。
;;;;;;;;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.
(define-datatype expval expval?
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

(define-datatype proc proc?
  (procedure
   (bvar symbol?)
   (body expression?)
   (env environment?)))

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval expval?)
   (saved-env environment?))
  (extend-env-rec
   (p-name symbol?)
   (b-var symbol?)
   (p-body expression?)
   (saved-env environment?)))

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
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)   
    
    (expression
     ("proc" "(" (separated-list identifier ":" type ",")")" expression)
     proc-exp)
    
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    
    (expression
     ("letrec"
      (separated-list type identifier "(" (separated-list identifier ":" type ",")")" "=" expression ";")
      "in" expression)
     letrec-exp)
    
    (type
     ("int")
     int-type)
    
    (type
     ("bool")
     bool-type)
    
    (type
     ("refto" type)
     refto-type) ;; 好吧，这就是所谓的引用类型
    
    (type
     ("void")
     void-type)
     
    
    (type
     ("(" (arbno type) "->" type ")") ;; 好吧!所谓的type居然已经出现在了这里,真是够吃惊的啦。
     proc-type)

    ;; 下面是新加入的语法
    (expression
     ("newref" "(" expression")")
     newref-exp)

    (expression
     ("deref" "(" expression ")") ;; 解引用
     deref-exp)

    (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;; type ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; check-equal-type! : Type * Type * Exp -> Unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp)
        #f)))

;; report-unequal-types : Type * Type * Exp -> Unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-qual-type!
                "Types didn't match : ~s != ~a in\n~a"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

;; type-to-exteranl-form : Type -> List
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
      (refto-type (ty)
                  (list
                   'refto
                   (type-to-external-form ty)))
      (void-type () 'void)
      )))

;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1) (type-of exp1 (init-tenv))))))

;; type-of : Exp * Tenv -> Type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
                (let ([ty1 (type-of exp1 tenv)]
                      [ty2 (type-of exp2 tenv)])
                  (check-equal-type! ty1 (int-type) exp1)
                  (check-equal-type! ty2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                  (let ([ty1 (type-of exp1 tenv)])
                    (check-equal-type! ty1 (int-type) exp1)
                    (bool-type)))
      
      (if-exp (exp1 exp2 exp3)
              (let ([ty1 (type-of exp1 tenv)]
                    [ty2 (type-of exp2 tenv)]
                    [ty3 (type-of exp3 tenv)])
                (check-equal-type! ty1 (bool-type) exp1)
                (check-equal-type! ty2 ty3 exp)
                ty2))
    
      (let-exp (vars exps body)
               (let ([exps-types (map (lambda (exp1) (type-of exp1 tenv)) exps)])
                 ;(eopl:printf "let-exp :\n vars -> ~a\n exps -> ~a\n" vars exps-types)
                 (type-of body
                          (extend-tenv* vars exps-types tenv))))
      
      
      (proc-exp (vars var-types body)
                (let ([result-type (type-of body
                                            (extend-tenv* vars var-types tenv))])
                  (proc-type var-types result-type)))
    
      (call-exp (rator rands)
                (let ([rator-type (type-of rator tenv)]
                      [rands-types (map (lambda (rand) (type-of rand tenv)) rands)])
                  (cases type rator-type
                    (proc-type (arg-types result-type)
                               (begin
                                 (check-equal-type!* arg-types rands-types rands)
                                 result-type))
                    (else
                     (report-rator-not-a-proc-type rator-type rator)))))
      
      (letrec-exp (p-result-types p-names b-vars b-var-types
                                  p-bodies letrec-body)
                  (eopl:printf "letrec-exp :\n p-names -> ~a\n b-vars -> ~a\n b-var-types -> ~a\n p-result-types -> ~a\n p-bodies -> ~a\n"
                               p-names b-vars b-var-types p-result-types p-bodies)
                  (let ([tenv-for-letrec-body
                         (extend-proc-type* p-names b-var-types p-result-types tenv)])
                    (eopl:printf "letrec-exp :\n tenv-for-letrec-body -> ~a\n" tenv-for-letrec-body)
                    (let ([p-body-types ;; 好吧,这也是很复杂的一个过程
                           (type-of-bodies p-bodies b-vars b-var-types tenv)])
                      (check-equal-type!*
                       p-body-types p-result-types p-bodies)
                      (type-of letrec-body tenv-for-letrec-body))))
      (newref-exp (exp1)
                  (let ([ty1 (type-of exp1 tenv)])
                    (refto-type ty1))) ;; 好吧，这里有了一个引用类型
      (deref-exp (exp1)
                 (let ([ty1 (type-of exp1 tenv)])
                   (cases type ty1
                     (refto-type (ty) ty)
                     (else (eopl:printf "~a is not a reference!\n" exp1)))))
      (setref-exp (exp1 exp2)
                  (let ([ty1 (type-of exp1 tenv)]
                        [ty2 (type-of exp2 tenv)])
                    (cases type ty1
                      (refto-type (ty)
                                  (check-equal-type! ty2 ty exp2)
                                  (void-type))
                      (else (eopl:printf "~a is not a reference!\n" exp1)))))

      
      )))


;;;;;;;;;;;;;;;;;;;; helper function ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define check-equal-type!*
  (lambda (p-bodies-types p-result-types p-bodies)
    (eopl:printf "check-equal-type!* :\n p-bodies-types -> ~a\n p-result-types -> ~a\n p-bodies -> ~a\n " p-bodies-types p-result-types p-bodies)
    (if (null? p-bodies-types)
        #t
        (begin
          (check-equal-type! (car p-bodies-types) (car p-result-types) (car p-bodies))
          (check-equal-type!* (cdr p-bodies-types) (cdr p-result-types) (cdr p-bodies))))))

(define type-of-bodies
  (lambda (bodies b-vars b-var-types tenv)
    (eopl:printf "type-of-bodies :\n bodies -> ~a\n b-vars -> ~a\n b-var-types -> ~a\n" bodies b-vars b-var-types)
    (if (null? bodies) '()
        (cons (type-of (car bodies) (extend-tenv* (car b-vars) (car b-var-types) tenv))
              (type-of-bodies (cdr bodies) (cdr b-vars) (cdr b-var-types) tenv)))))

(define extend-proc-type*
  (lambda (p-names b-var-types p-result-types tenv)
    (if (null? p-names)
        tenv
        (extend-proc-type*
         (cdr p-names) (cdr b-var-types)  (cdr p-result-types)
         (extend-tenv (car p-names)
                      (proc-type (car b-var-types) (car p-result-types))
                      tenv)))))

(define extend-tenv*
  (lambda (vars types tenv)
    (eopl:printf "extend-tenv* :\n vars -> ~a\n types -> ~a\n tenv -> ~a\n" vars types tenv)
    (if (null? vars) tenv
        (extend-tenv* (cdr vars)
                      (cdr types)
                      (extend-tenv (car vars) (car types) tenv)))))

(define report-rator-not-a-proc-type
    (lambda (rator-type rator)
      (eopl:error 'type-of-expression
        "Rator not a proc type:~%~s~%had rator type ~s"   
           rator 
           (type-to-external-form rator-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; type environments ;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extend-tenv-record
   (sym symbol?)
   (atype type?)
   (tenv type-environment?)))

(define empty-tenv empty-tenv-record)
(define extend-tenv extend-tenv-record)

(define apply-tenv
  (lambda (tenv sym)
    (cases type-environment tenv
      (empty-tenv-record ()
                         (eopl:error 'apply-tenv "Unbound variable ~s" sym))
      (extend-tenv-record (sym1 val1 old-env)
                            (if (eqv? sym sym1)
                                val1
                                (apply-tenv old-env sym))))))
(define init-tenv
  (lambda ()
    (extend-tenv 'x (int-type)
                 (extend-tenv 'v (int-type)
                              (empty-tenv)))))

;; test code
(type-of-program (scan&parse "newref(10)"))
(type-of-program (scan&parse "deref(newref(10))"))
(type-of-program (scan&parse "setref(newref(10), 10)"))
                           
