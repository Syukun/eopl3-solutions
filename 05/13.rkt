#lang eopl
(require "./base/helper.rkt")
;; Translate the definitions of fact and fact-iter into the LETREC language.
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
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?))
  (mult1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (mult2-cont
   (val1 expval?)
   (cont continuation?))
  (rator1-cont
   (rands list?)
   (env environment?)
   (cont continuation?))
  (rand1-cont
   (rands list?)
   (env environment?)
   (cont continuation?)
   (rator expval?)
   (acc list?))

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
      (diff1-cont (exp2 env cont)
                  (value-of/k exp2 env
                              (diff2-cont val cont)))
      (diff2-cont (val1 cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (apply-cont cont
                                (num-val (- num1 num2)))))
      (mult1-cont (exp2 env cont)
                  (value-of/k exp2 env
                              (mult2-cont val cont)))
      (mult2-cont (val1 cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (apply-cont cont
                                (num-val (* num1 num2)))))
      (rator1-cont (rands env cont)
                   (value-of/k (car rands) env (rand1-cont (cdr rands) env cont val '())))
      (rand1-cont (rands env cont rator acc)
                  (if (null? rands)
                      (let [(proc1 (expval->proc rator))]
                        (apply-procedure*/k proc1 (append acc (list val)) cont))
                      (value-of/k (car rands) env
                                  (rand1-cont (cdr rands) env cont rator (append acc (list val))))
                          )))))

;; value-of-program : Program -> FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (end-cont))))))

;; new stuff
(define exp->readable
  (lambda (exp)
    (cases expression exp
      (const-exp (num) (eopl:printf "const-exp : num -> ~a.\n" num))
      (var-exp (var) (eopl:printf "var-exp : var -> ~a.\n" var))
      (proc-exp (var body) (eopl:printf "proc-exp : var -> ~a.\n" var))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (eopl:printf "letrec-exp\n"))
      (zero?-exp (exp1) (eopl:printf "zero?-exp\n"))
      (let-exp (var exp1 body) (eopl:printf "let-exp\n"))
      (if-exp (exp1 exp2 exp3) (eopl:printf "if-exp\n"))
      (diff-exp (exp1 exp2) (eopl:printf "diff-exp\n"))
      (call-exp (rator rand) (eopl:printf "call-exp\n"))
      (else "other"))))

(define cont->readable
  (lambda (cont)
     (cases continuation cont
       (end-cont () (eopl:printf "end-cont\n"))
       (zero1-cont (saved-cont) (eopl:printf "zero1-cont\n"))
       
       (let-exp-cont (var body saved-env saved-cont) (eopl:printf "let-exp-cont : Start working on let-body\n"))
       (if-test-cont (exp2 exp3 saved-env saved-cont) (eopl:printf "if-test-cont : Start working on exp1\n"))
       
       (diff1-cont (exp2 saved-env saved-cont) (eopl:printf "Start woring on first oprand\n"))
       (diff2-cont (val1 saved-cont) (eopl:printf "Send val value of <<~a>> to continuation\n" val1))
       
       (mult1-cont (exp2 env cont) (eopl:printf "mult1-cont : Start working on first oprand\n"))
       (mult2-cont (val1 cont) (eopl:printf "mult2-cont : Send val value of <<~a>> to continuation\n" val1))
       
       (rator1-cont (rands env cont) (eopl:printf "rator1-cont : Start working on oprands\n"))
       (rand1-cont (rands env cont rator acc) (eopl:printf "rator2-cont : Start working on oprands\n"))
       (else (eopl:printf "other-cont\n")))))

;; value-of/k : Exp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (begin
      (newline)
      ;(exp->readable exp)
      (cont->readable cont)
      (cases expression exp
        (const-exp (num) (apply-cont cont (num-val num)))
        (var-exp (var) (apply-cont cont (apply-env env var)))
        (proc-exp (var-list body)
                  (apply-cont cont
                              (proc-val (procedure var-list body env))))
        (letrec-exp (p-name b-vars p-body letrec-body)
                    (value-of/k letrec-body
                                (extend-env-rec p-name b-vars p-body env)
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
        (mult-exp (exp1 exp2)
                  (value-of/k exp1 env
                              (mult1-cont exp2 env cont)))
        (call-exp (rator rand)
                  (value-of/k rator env
                              (rator1-cont rand env cont)))
        ))))

;; apply-procedure/k : Proc * ExpVal * Cont -> FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var val saved-env)
                             cont)))))
;; apply-procedure*/k : Proc * ExpValList * Cont -> FinalAnswer
(define apply-procedure*/k
  (lambda (proc1 val-list cont)
    (cases proc proc1
      (procedure (var-list body saved-env)
                 (value-of/k body
                             (extend-env* var-list val-list saved-env)
                             cont)))))
;; extend-env* : VarList * ExpValList * Env -> Env
(define extend-env*
  (lambda (var-list val-list env)
    (if (null? var-list) env
        (extend-env* (cdr var-list) (cdr val-list)
                     (extend-env (car var-list) (car val-list) env)))))
 
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
    (expression ("*" "(" expression "," expression ")") mult-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec"  (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)

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
   (p-name (list-of symbol?))
   (b-vars (list-of (list-of symbol?)))
   (p-body (list-of expression?))
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
          (extend-env-rec (p-names b-vars p-bodies saved-env)
                            (cond
                             ((location search-sym p-names) ;; 查找函数名
                              => (lambda (n) ;; 如果前面的location函数返回了一个数
                                    (proc-val ;; 构造出一个函数
                                     (procedure
                                      (list-ref b-vars n) ;; 我没有看错吧,居然直接调用list的函数来取形式参数
                                      (list-ref p-bodies n) ;; 和对应的函数体
                                      env))))
                             (else (apply-env saved-env search-sym)))))))

(define location
  (lambda (sym syms) ;; sym是要搜寻的东西
    (cond
     ((null? syms) #f)
     ((eqv? sym (car syms)) 0)
     ((location sym (cdr syms)) ;; 继续往下找,总之location函数要么返回false,要么返回一个数嘛
      => (lambda (n) ;; 如果返回了一个数,说明要查找的这个玩意的深度要在返回的深度的基础上加1
           (+ n 1)))
     (else #f))))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code
(run "letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n, 1))) in (fact 4)")
(run "letrec
          fact-iter(n) = (fact-iter-acc n 1)
          fact-iter-acc(n, a) = if zero?(n) then a else (fact-iter-acc -(n, 1) *(n, a))
      in (fact-iter 4)")




