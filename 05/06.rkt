#lang eopl
(require "./base/helper.rkt")
;; Add list to the language.
(define identifier? symbol?)

;;;;;;;;;;;;;;;;;;;;;;;;;continuation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (rator-cont
   (rand expression?)
   (env environment?)
   (cont continuation?))
  (rand-cont
   (rand expval?)
   (cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?))
  (cons1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (cons2-cont
   (val1 expval?)
   (cont continuation?))
  (car-cont
   (cont continuation?))
  (cdr-cont
   (cont continuation?))
  (null-cont
   (cont continuation?))
  (list1-cont
   (exp-list (list-of expression?))
   (env environment?)
   (cont continuation?))
  (list2-cont
   (exp-list (list-of expression?))
   (env environment?)
   (cont continuation?)
   (acc expval?))
   
  )

;; apply-cont : Cont * ExpVal -> FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (begin
                  (eopl:printf "End of computation.~%")
                  val))
      (zero1-cont (saved-cont)
                  (apply-cont saved-cont
                              (bool-val (zero? (expval->num val)))))
      (let-exp-cont (var body saved-env saved-cont)
                    (value-of/k body (extend-env var val saved-env) saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                          (if (expval->bool val)
                              (value-of/k exp2 saved-env saved-cont)
                              (value-of/k exp3 saved-env saved-cont)))
      (rator-cont (rand env cont)
                  (value-of/k rand env (rand-cont val cont)))
                  
      (rand-cont (val1 cont)
                   (let ((proc1 (expval->proc val1)))
                     (apply-procedure/k proc1 val cont)))
      (diff1-cont (exp2 env cont)
                  (value-of/k exp2 env
                              (diff2-cont val cont)))
      (diff2-cont (val1 cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (apply-cont cont
                                (num-val (- num1 num2)))))
      (cons1-cont (exp2 env cont)
                  (value-of/k exp2 env (cons2-cont val cont)))
      (cons2-cont (val1 cont)
                  (apply-cont cont (pair-val val1 val)))
      (car-cont (cont)
                (apply-cont cont
                            (expval->car val)))
      (cdr-cont (cont)
                (apply-cont cont
                            (expval->cdr val)))
      (null-cont (cont)
                (apply-cont cont
                            (expval->null? val)))
      (list1-cont (exp-list env cont)
                  (begin
                    ;(print "exp-list -> " exp-list)
                    (value-of/k (last-element exp-list) env
                                (list2-cont (except-last-element exp-list) env cont
                                          (pair-val val (emptylist-val)))))) 
      
      (list2-cont (exp-list env cont acc)
                (if (null? exp-list) (apply-cont cont (pair-val val acc))
                    (value-of/k (last-element exp-list) env
                                (list2-cont (except-last-element exp-list) env
                                          cont (pair-val val acc)))))
                          )))
;; 可不可以考虑相互递归呢?
(define (last-element a-list)
  (if (null? (cdr a-list)) (car a-list)
      (last-element (cdr a-list))))

(define (except-last-element a-list)
  (if (null? (cdr a-list)) '()
      (cons (car a-list) (except-last-element (cdr a-list)))))
    

           
      

;; value-of-program : Program -> FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (end-cont))))))

;; value-of/k : Exp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (apply-env env var)))
      (proc-exp (var body)
                (apply-cont cont
                            (proc-val (procedure var body env))))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of/k letrec-body
                              (extend-env-rec p-name b-var p-body env)
                              cont))

      (zero?-exp (exp1)
                 (value-of/k exp1 env
                             (zero1-cont cont)))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont)))
      (let-exp (var exp1 body)
                 (value-of/k exp1 env
                             (let-exp-cont var body env cont)))
      (diff-exp (exp1 exp2)
                 (value-of/k exp1 env
                             (diff1-cont exp2 env cont)))
      (call-exp (rator rand)
                  (value-of/k rator env
                              (rator-cont rand env cont)))
      (list-exp (exp-list)
                 (if (null? exp-list) (apply-cont cont (emptylist-val))
                     (value-of/k (last-element exp-list) env
                                 (list1-cont (except-last-element exp-list) env cont))))
      
      (cons-exp (exp1 exp2) ;; 先实现cons表达式吧!
                (value-of/k exp1 env
                            (cons1-cont exp2 env cont)))
      (car-exp (exp1)
               (value-of/k exp1 env
                           (car-cont cont)))
      (cdr-exp (exp1)
               (value-of/k exp1 env
                           (cdr-cont cont)))
      (null?-exp (exp1)
                (value-of/k exp1 env
                            (null-cont cont)))
      (emptylist-exp ()
                     (apply-cont cont (emptylist-val)))
      )))

;; apply-procedure/k : Proc * ExpVal * Cont -> FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var val saved-env)
                             cont)))))
 
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
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    ;; about list
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (pair-val ;; 好吧,这玩意主要是给pair类型准备的。
   (first expval?)
   (rest expval?))
  (emptylist-val))

;;; extractors

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

;; expval->car 返回pair-val的前部分的值
(define expval->car
  (lambda (v)
    (cases expval v
	   (pair-val (car cdr) car)
	   (else (expval-extractor-error 'car v)))))

;; expval->cdr 返回后半部分的值
(define expval->cdr
  (lambda (v)
    (cases expval v
	   (pair-val (car cdr) cdr)
	   (else (expval-extractor-error 'cdr v)))))

;; expval->null? 用于判断一个list是否为空
(define expval->null?
  (lambda (v)
    (cases expval v
	   (emptylist-val () (bool-val #t))
	   (else (bool-val #f)))))

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

;;;;;;;;;;;;;;;; environment structures ;;;;;;;;;;;;;;;;
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

(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;
(define apply-env
  (lambda (env search-sym)
    (cases environment env
           (empty-env ()
                      (eopl:error 'apply-env "No binding for ~s" search-sym))
           (extend-env (var val saved-env)
                       (if (eqv? search-sym var)
                           val
                           (apply-env saved-env search-sym)))
           (extend-env-rec (p-name b-var p-body saved-env)
                           (if (eqv? search-sym p-name)
                               (proc-val (procedure b-var p-body env))
                               (apply-env saved-env search-sym))))))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code
(run "list(1, 2, 3, 4, 5, 6)")

