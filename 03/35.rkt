#lang eopl
;;;;;;;;;;;;;;;;;;environments;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 没办法，environment interface必须要重写
;; empty-env : () -> Env
(define empty-env
  (lambda () (list 'empty-env)))

;; extend-env : Var * SchemeVar * Env -> Env
(define extend-env
  (lambda (var val env)
    (begin
      (print "extend-env val -> " val)
      (list 'extend-env var val env))))

;; extend-env-rec : Name * Var * Var * Env -> Env
(define extend-env-rec ;; 这个提高了效率
  (lambda (p-name b-var body saved-env)
    (let [(vec (make-vector 1))]
      (let [(new-env (extend-env p-name vec saved-env))] ;; 构建一个新的env，但是val的部分改为了长度为1的vector
        (vector-set! vec 0 ;; 该vector里面装着闭包，这样比之前提高了效率，因为不用每次查找函数的时候重新再构造一个procval，直接从vector里面取即可
                     (proc-val (procedure b-var body new-env)))
        new-env))))

;; apply-env : Env * Var -> SchemeVal
(define apply-env
  (lambda (env search-var)
    (cond
      [(eqv? (car env) 'empty-env) (report-no-binding-found search-var)]
      [(eqv? (car env) 'extend-env) (let [(saved-var (cadr env))
                                          (saved-val (caddr env))
                                          (saved-env (cadddr env))]
                                      (if (eqv? search-var saved-var)
                                          (if (vector? saved-val) ;; 如果saved-val部分是一个vector，说明search-var映射到了一个函数
                                              (vector-ref saved-val 0) ;; 从vector中提取出闭包
                                              saved-val);; 否则的话直接返回saved-val
                                              (apply-env saved-env search-var)))]
      [else (report-invalid-env env)])))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define identifier? symbol?) 



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
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression")") call-exp)
    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (var symbol?) ;; 只支持一个参数
   (body expression?)
   (env list?)
   ))

;;
(define-datatype letproc letproc?
  (letp
   (body expression?)))

;;; an expressed value is either a number, a boolean or a procval.
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?)))

;;; extractors:
;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (begin
      (print "expval->num v -> " v)
      (cases expval v
        (num-val (num) num)
        (else (expval-extractor-error 'num v))))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
           (bool-val (bool) bool)
           (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
           (proc-val (proc) proc)
           (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (begin
      (print "apply-procedure : proc1 --> " proc1)
      (print "apply-procedure : val -->" val)
      (cases proc proc1
	     (procedure (var body saved-env)
			(begin
			  (print "apply-procedure : var --> " var)
			  (print "apply-procedure : body --> " body )
			  (print "apply-procedure : new-env --> " (extend-env var val saved-env))
			  (value-of body (extend-env var val saved-env))))
	     ))))

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;
(define init-env
  (lambda ()
    (empty-env)))

;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 (init-env))))))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
           (const-exp (num) (num-val num))
           (var-exp (var) (apply-env env var))
           (diff-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val
                          (- num1 num2)))))

           (zero?-exp (exp1)
                      (let ((val1 (value-of exp1 env)))
                        (begin
                          (print "zero?-exp val1 -> " val1)
                          (let ((num1 (expval->num val1)))
                            (begin
                              (print "zero?-exp num1 -> " num1)
                              (if (zero? num1)
                                  (bool-val #t)
                                  (bool-val #f)))))))

           (if-exp (exp1 exp2 exp3)
                   (begin
                      (print "if-exp exp1 ->" exp1)
                      (let ((val1 (value-of exp1 env)))
                        (begin
                          (print "if-exp val1 ->" val1)
                          (if (expval->bool val1)
                              (value-of exp2 env)
                              (value-of exp3 env))))))

           (let-exp (var exp1 body)
                    (let ((val1 (value-of exp1 env)))
                      (begin
                        (print "let-exp var1 --> " val1)
                        (value-of body
                                  (extend-env var val1 env)))))
           (proc-exp (var body)
		     (begin
		       (print "proc-exp : var --> " var) 
		       (print "proc-exp : body --> " body)
		       ;(procedure var body env)
		       (proc-val (procedure var body env))
		       )) 
	   (call-exp (rator rand)
		     (begin
		       (print "call-exp : rand --> " rand)
		       (print "call-exp : (expval->proc (value-of rator env)) --> " (expval->proc (value-of rator env)))
		       (let ((proc (expval->proc (value-of rator env)))
			     (args (value-of rand env)))
			 (begin
			   (print "call-exp : proc --> " proc)
			   (print "call-exp : args --> " args)
			   (apply-procedure proc args)))))
           )))

;; extend-env-with-proc
(define (extend-env-with-proc names vars bodies env)
  (if (null? names)
      env
      (extend-env-with-proc (cdr names)
			    (cdr vars)
			    (cdr bodies)
			    (extend-env (car names)
					(letp (car bodies))
					env))))
;; run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
;; print 
;; 自定义的辅助函数,输出打印信息
(define (print arg1 arg2)
  (begin
    (newline)
    (newline)
    (display arg1)
    (display arg2)
    (newline)))

;; test-code
(run "let g = proc (x) if zero?(x) then 1 else 0 in (g 1)")





