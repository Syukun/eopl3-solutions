#lang eopl
(require "./base/helper.rkt")
;; About trampoline.
;; Modify the trampolied interpreter to wrap (lambda () ...) around each call to apply-procedure/k.
;; 修改之后不用更改contracts，因为此时形成了一个bounce，在trampoline中会调用该bounce，所以程序会继续运行下去。
(define debug #t)

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
                    (begin
                      (eopl:printf "let-exp-cont :\n var -> ~a\n body -> ~a\n\n" var body)
                      (value-of/k body (extend-env var val saved-env) saved-cont)))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                          (if (expval->bool val)
                              (value-of/k exp2 saved-env saved-cont)
                              (value-of/k exp3 saved-env saved-cont)))
      (rator-cont (rand env cont)
                  (begin
                    (eopl:printf "rator-cont :\n rand -> ~a\n proc -> ~a\n cont -> ~a\n\n" rand val cont)
                    (value-of/k rand env (rand-cont val cont))))
                  
      (rand-cont (val1 cont)
                 (begin
                   (eopl:printf "rand-cont :\n val1 -> ~a\n proc -> ~a\n cont -> ~a\n\n" val1 val cont)
                   (let ((proc1 (expval->proc val1)))
                     (lambda ()
                     (apply-procedure/k proc1 val cont)))))
      (diff1-cont (exp2 env cont)
                  (value-of/k exp2 env
                              (diff2-cont val cont)))
      (diff2-cont (val1 cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (apply-cont cont
                                (num-val (- num1 num2)))))
                          
                          )))

;; value-of-program : Program -> FinalAnswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (trampoline
                  (begin
                    ;(eopl:printf "Inside value-of-program\n")
                    (value-of/k exp1 (init-env) (end-cont))))))))
;; trampoline : Bounce -> FinalAnswer
(define trampoline
  (lambda (bounce)
    (begin
      (eopl:printf "Inside trampoline :\n bounce -> ~a\n" bounce)
      (if (expval? bounce)
          bounce
          (trampoline (bounce))))))

;; value-of/k : Exp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var)
               (begin
                 (eopl:printf "var-exp :\n var -> ~a\n\n" var)
                 (apply-cont cont (apply-env env var))))
      (proc-exp (var body)
                (begin
                  (eopl:printf "proc-exp :\n var -> ~a\n body -> ~a\n\n" var body)
                  (apply-cont cont
                              (proc-val (procedure var body env)))))
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
               (begin
                 (eopl:printf "let-exp :\n var -> ~a\n exp1 -> ~a\n body -> ~a\n\n" var exp1 body)
                 (value-of/k exp1 env
                             (let-exp-cont var body env cont))))
      (diff-exp (exp1 exp2)
                 (value-of/k exp1 env
                             (diff1-cont exp2 env cont)))
      (call-exp (rator rand)
                (begin
                  (eopl:printf "call-exp :\n rator -> ~a\n rand -> ~a\n\n" rator rand)
                  (value-of/k rator env
                              (rator-cont rand env cont))))
      )))

;; apply-procedure/k : Proc * ExpVal * Cont -> FinalAnswer
;; 这里以下面的代码为例:
;; let p = proc (x) -(x, 1) in (p (p (p 1)))
;; 首先进入 let-exp
;; 然后进入 proc-exp
;; 进入 let-exp-cont,扩展了env(将p映射到proc)，然后求letbody的值，调用value-of/k
;; 进入 call-exp,求rator的值，进入var-exp,取出函数值,调用rator-cont
;; 现在要求rand的值，此时存入了rator-cont,当然此时rand也是调用，
;; 进入call-exp,求rator的值,进入var-exp,取出函数值,调用rator-cont
;; 现在继续要求rand的值,此时再次存入了rator-cont,继续...
;; 现在调用到了(p 1),进入call-exp,求rator的值,进入var-exp,取出函数值,调用rator-cont
;; 现在继续要求rand的值,好的，进入到num-exp,现在求出来了等于(num-val 1) ,此时的cont里面就像堆栈一样铺满了下面要运算的东西
;; num-exp中调用apply-cont,进入rand-exp
;; 好吧，进入apply-procedure/k,也就是返回了一个无参数的函数，作为最后的结果传递给trampoline
;; 好吧，其实也就是这样啦，没什么大不了的。
;; 所谓的trampoline不过是为了避免堆栈溢出弄的一个东东，每次到函数调用的时候，就将调用封装成一个bounce，返回回来，这样做的好处在于避免了堆栈过大

(define apply-procedure/k ;; 每次调用apply-procedure/k都会返回一个无参数的函数，这里有一点是很重要的，由于返回的是一个过程，也就是说
  (lambda (proc1 val cont)
    (lambda ()
      (cases proc proc1
        (procedure (var body saved-env)
                   (value-of/k body
                               (extend-env var val saved-env)
                               cont))))))
 
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
(run "let p = proc (x) -(x, 1) in (p (p (p 1)))")




