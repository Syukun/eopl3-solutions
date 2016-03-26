#lang eopl
;; 修改language，是的当函数被调用的时候发现参数的个数不对头的话，立马raise exception
;; 好吧，我们现在要实现函数可以包含多个参数，其实这个玩意已经写过很多遍了。

(define identifier? symbol?)
;;;;;;;;;;;;;;;;;;;;;;;;;continuation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype continuation continuation?
  (end-cont)                      
  (diff1-cont                    
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont                     
   (val1 expval?)
   (cont continuation?))
  (unop-arg-cont
   (unop unary-op?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (rator-cont          
   (rands (list-of expression?)) ;; 因为有很多个参数
   (saved-vals (list-of expression?)) ;; 所谓的已经计算出了结果的结果列表
   (env environment?)
   (cont continuation?))
   (rand-cont
    (proc-val expval?)
    (rands (list-of expression?))
    (saved-vals (list-of expval?))
    (saved-env  environment?)
    (saved-cont continuation?))                    
  (try-cont
   (var symbol?)
   (handler-exp expression?)
   (env environment?)
   (cont continuation?))
  (raise1-cont
   (saved-cont continuation?))
  )


;; value-of-program : Program -> ExpVal
(define value-of-program 
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (value-of/k body (init-env) (end-cont))))))

 ;; value-of/k : Exp * Env * Cont -> FinalAnswer
  ;; Page: 173
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      
      (const-exp (num) (apply-cont cont (num-val num)))
      
      (const-list-exp (nums)
                      (apply-cont cont
                                  (list-val (map num-val nums))))
      
      (var-exp (var) (apply-cont cont (apply-env env var)))
      
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (diff1-cont exp2 env cont)))
      
      (unop-exp (unop exp1)
                (value-of/k exp1 env
                            (unop-arg-cont unop cont)))
      
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont)))
      ;; 好吧，要开始改变这里的东西啦！
      (proc-exp (vars body)
                (eopl:printf "proc-exp :\n vars -> ~a\n body -> ~a\n\n" vars body)
                (apply-cont cont
                            (proc-val (procedure vars body env))))
      
      (call-exp (rator rands)
                (eopl:printf "call-exp :\n rator -> ~a\n rand -> ~a\n\n" rator rands)
                (value-of/k rator env
                            (rator-cont rands '() env cont)))
      
      (let-exp (var exp1 body) ;; val为参数
               (eopl:printf "let-exp :\n 将let表达式转换为call表达式 :\n\n ~a <==>\n ~a\n\n" exp
                            (call-exp (proc-exp (list  var) body) (list exp1)))
               (value-of/k
                (call-exp (proc-exp (list var) body) (list exp1)) 
                env
                cont))
      
      (letrec-exp (p-name b-vars p-body letrec-body)
                  (value-of/k
                   letrec-body
                   (extend-env-rec p-name b-vars p-body env)
                   cont))
      
      (try-exp (exp1 var handler-exp)
               (value-of/k exp1 env
                           (try-cont var handler-exp env cont)))
      
      (raise-exp (exp1)
                 (value-of/k exp1 env
                             (raise1-cont cont))))))

;; apply-cont : continuation * expval -> final-expval
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (begin
                  (eopl:printf
                   "End of computation.~%")
                  val))
      (diff1-cont (exp2 saved-env saved-cont)
                  (value-of/k exp2 saved-env (diff2-cont val saved-cont)))
      (diff2-cont (val1 saved-cont)
                  (let ((n1 (expval->num val1))
                        (n2 (expval->num val)))
                    (apply-cont saved-cont
                                (num-val (- n1 n2)))))
      (unop-arg-cont (unop cont)
                     (apply-cont cont
                                 (apply-unop unop val)))
      
      (if-test-cont (exp2 exp3 env cont)
                    (if (expval->bool val)
                        (value-of/k exp2 env cont)
                        (value-of/k exp3 env cont)))
      ;; new-stuff
      (rator-cont (rands saved-vals saved-env saved-cont)
                  (value-of/k (car rands) saved-env
                              (rand-cont val (cdr rands) saved-vals
                                         saved-env saved-cont)))
      (rand-cont (proc-val rands saved-vals saved-env saved-cont)
                 (if (null? rands)
                     (let [(proc (expval->proc proc-val))]
                       (let [(new-vals (append saved-vals (list val)))
                             (require-vals (expval->rators proc-val))] ;; require-vals是从proc-val中取出参数的列表
                       (if (equal? (length require-vals) (length new-vals)) ;; 比较形参和实参的个数
                           (apply-procedure/k proc new-vals saved-cont) ;; 如果相等，可以继续运行下去
                           (begin
                             (eopl:printf "required args: ~a\n given: ~a\n"require-vals new-vals)
                             (apply-cont (raise1-cont saved-cont) (list-val saved-vals))))));; 否则的话，抛出异常，直接将计算完成的参数作为raise的值，也对
                     (value-of/k (car rands) saved-env
                                 (rand-cont proc-val (cdr rands) 
                                            (append saved-vals (list val)) saved-env
                                            saved-cont))))
      ;; the body of the try finished normally-- don't evaluate the handler
      (try-cont (var handler-exp saved-env saved-cont)
                (apply-cont saved-cont val))
      ;; val is the value of the argument to raise
      (raise1-cont (saved-cont)
                   ;; we put the short argument first to make the trace more readable.
                   (apply-handler val saved-cont))
      )))

;; apply-procedure/k : procedure * expval * cont -> final-expval
(define apply-procedure/k
  (lambda (proc1 args cont)
    (cases proc proc1
           (procedure (vars body saved-env)
                      (value-of/k body
                                  (extend-env* vars args saved-env)
                                  cont)))))
;;new stuff
(define extend-env*
  (lambda (vars vals saved-env)
    (if (null? vars)
        saved-env
        (extend-env* (cdr vars) (cdr vals)
                     (extend-env (car vars) (car vals) saved-env)))))


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
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)

    ;; 关于函数和函数调用
    (expression ("proc" "(" (separated-list identifier ",") ")" expression)  proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    
    (expression ("letrec" identifier "(" (arbno identifier) ")" "=" expression "in" expression) letrec-exp)
    ;; 一谈到异常处理,我还很兴奋呢!
    (expression ("try" expression "catch" "(" identifier ")" expression) try-exp)
    (expression ("raise" expression) raise-exp)
    (expression (unary-op "(" expression ")") unop-exp) ;; 这个unary-op非常有意思
    (unary-op ("null?") null?-unop)
    (unary-op ("car") car-unop)
    (unary-op ("cdr") cdr-unop)
    (unary-op ("zero?") zero?-unop)
    ;; Lists. We will have lists of literal number only.
    (expression ("list" "(" (separated-list number ",") ")") const-list-exp)
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
  (list-val
   (lst (list-of expval?)))
   )

;;; extractors
(define expval->list
  (lambda (v)
    (cases expval v
      (list-val (lst) lst)
      (else (expval-extractor-error 'list v)))))

    
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

(define expval->rators
  (lambda (v)
    (cases expval v
      (proc-val (a-proc)
                (cases proc a-proc
                  (procedure (bval body env) bval)
                  (else (eopl:error "bad condition!\n"))))
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
   (b-var (list-of symbol?))
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

(define apply-handler
  (lambda (val cont)
    (cases continuation cont
     ;; interesting cases
      (try-cont (var handler-exp saved-env saved-cont)
                (value-of/k handler-exp
                            (extend-env var val saved-env)
                            saved-cont))
      (end-cont ()
                (report-uncaught-exception)) ;; 未被捕获到的异常
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (apply-handler val saved-cont))
      (diff1-cont (exp2 saved-env saved-cont)
                  (apply-handler val saved-cont))
      (diff2-cont (val1 saved-cont)
                  (apply-handler val saved-cont))
      (rator-cont (rands saved-vals saved-env saved-cont)
                  (apply-handler val saved-cont))
      (rand-cont (proc-val rands saved-vals saved-env saved-cont)
                 (apply-handler val saved-cont))
      (raise1-cont (cont)
                   (apply-handler val cont))
      (unop-arg-cont (unop saved-cont)
                     (apply-handler val saved-cont))
      )))

(define report-uncaught-exception
  (lambda ()
    (eopl:error 'apply-handler "uncaught exception!")))

(define apply-unop
  (lambda (unop val)
    (cases unary-op unop
      (null?-unop ()
                  (bool-val
                   (null? (expval->list val))))
      (car-unop ()
                (car (expval->list val)))
      (cdr-unop ()
                (list-val (cdr (expval->list val))))
      (zero?-unop ()
                  (bool-val
                   (zero? (expval->num val)))))))

;; test code
(run "let index =
               proc (n)
                 letrec inner (lst)
                  = if null?(lst)
                      then raise 99
                       else if zero?(-(car(lst), n))
                                 then 0
                                 else -((inner cdr(lst)), -1)
                  in proc (lst)
                      try (inner lst)
                        catch (x) -1
        in ((index 5) list(2, 3))")








