#lang eopl
;; ex-25 Registerize the interpreter for multiargument procedures.
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
   (rands (list-of expression?))
   (env environment?)
   (cont continuation?))
  (rand1-cont
   (rands (list-of expression?))
   (rator-val expval?)
   (saved-cont continuation?)
   (acc (list-of expval?)))
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
  )
(define exp 'uninitialized)
(define env 'uninitialized)
(define cont 'uninitialized)
(define val 'uninitialized)
(define proc1 'uninitialized)

;; value-of-program : Program -> FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (set! cont (end-cont))
                 (set! exp exp1)
                 (set! env (init-env))
                 (value-of/k)))))

;; value-of/k : () -> FinalAnswer
(define value-of/k
  (lambda ()
    (cases expression exp
      (const-exp (num)
                (set! val (num-val num))
                (apply-cont))
      (var-exp (var)
               (set! val (apply-env env var))
               (apply-cont))
      (proc-exp (var-list body)
                (eopl:printf "proc-exp :\n var-list -> ~a\n body -> ~a\n" var-list body)
                (set! val (proc-val (procedure var-list body env)))
                (apply-cont))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (set! exp letrec-body)
                  (set! env (extend-env-rec p-name b-var p-body env))
                  (value-of/k))
      (zero?-exp (exp1)
                 (set! cont (zero1-cont cont))
                 (value-of/k))
      (let-exp (var exp1 body)
               (eopl:printf "let-exp :\n var -> ~a\n exp1 -> ~a\n" var exp1) 
               (set! cont (let-exp-cont var body env cont))
               (set! exp exp1)
               (value-of/k))
      (if-exp (exp1 exp2 exp3)
              (set! cont (if-test-cont exp2 exp3 env cont))
              (set! exp exp1)
              (value-of/k))
      (diff-exp (exp1 exp2)
                (set! cont (diff1-cont exp2 env cont))
                (set! exp exp1)
                (value-of/k))
      (call-exp (rator rands)
                (eopl:printf "call-exp :\n rator -> ~a\n rands -> ~a\n" rator rands)
                (set! cont (rator-cont rands env cont))
                (set! exp rator)
                (value-of/k)))))

;; apply-cont : () -> FinalAnswer
(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.\n")
                val)
      (zero1-cont (saved-cont)
                  (set! cont saved-cont)
                  (set! val (bool-val (zero? (expval->num val))))
                  (apply-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (set! cont saved-cont)
                    (set! exp body)
                    (set! env (extend-env var val saved-env))
                    (value-of/k))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (set! cont saved-cont)
                    (if (expval->bool val)
                        (set! exp exp2)
                        (set! exp exp3))
                    (set! env saved-env)
                    (value-of/k))
      (diff1-cont (exp2 saved-env saved-cont)
                  (set! cont (diff2-cont val saved-cont))
                  (set! exp exp2)
                  (set! env saved-env)
                  (value-of/k))
      (diff2-cont (val1 saved-cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (set! cont saved-cont)
                    (set! val (num-val (- num1 num2)))
                    (apply-cont)))
     
      (rator-cont (rands saved-env saved-cont)
                  (eopl:printf "rator-cont :\n rands -> ~a\n" rands)
                  ;; 好吧，从现在开始要开始计算各个参数rands的值了
                  (set! cont (rand1-cont (cdr rands) val saved-cont '()))
                  (set! exp (car rands)) ;; 开始计算第一个参数的值
                  (set! env saved-env)
                  (value-of/k))
      (rand1-cont (rands rator-val saved-cont acc)
                  (eopl:printf "rand1-cont :\n acc -> ~a\n" acc)
                  ;; 然后要开始递归的计算每个参数的值
                  (if (null? rands) ;; 所有的东西都已经计算完成了
                      (let ((rator-proc (expval->proc rator-val)))
                        (begin
                          (set! cont saved-cont)
                          (set! proc1 rator-proc)
                          (set! val (append acc (list val)))
                          (apply-procedure/k)))
                      (begin
                        (set! cont (rand1-cont (cdr rands) rator-val saved-cont (append acc (list val))))
                        ;;(set! env env) ;; 这句话可以省略，确实没有很大的意义
                        (set! exp (car rands))
                        (value-of/k))))
              
                
      (rand-cont (rator-val saved-cont)
                 (let ((rator-proc (expval->proc rator-val)))
                   (set! cont saved-cont)
                   (set! proc1 rator-proc)
                   (set! val val)
                   (apply-procedure/k))))))

;; apply-procedure/k : () -> FinalAnswer
(define apply-procedure/k
  (lambda ()
    (cases proc proc1
      (procedure (var-list body saved-env)
                 (set! exp body)
                 (set! env (extend-env* var-list val saved-env))
                 (value-of/k)))))
;; extend-env*
(define (extend-env* var-list val-list env)
  (if (null? var-list) env
      (extend-env* (cdr var-list)
                   (cdr val-list)
                   (extend-env (car var-list) (car val-list) env))))

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
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)

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
   (proc proc?)))

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

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;
(define-datatype proc proc?
  (procedure
   (bvar (list-of symbol?))
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

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code
(run "let p = proc (x, y) -(x, y) in (p 1 2)")



