#lang eopl
;; 书中给出的实现并不高效，我们需要实现一个更加高效的版本，具体来说，就是在每一个continuation中加入try-cont
;; 这玩意调试起来非常困难啊！

(define identifier? symbol?)
;;;;;;;;;;;;;;;;;;;;;;;;;continuation;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-datatype continuation continuation?
  (end-cont)                      
  (diff1-cont                    
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (try-cont continuation?))
  (diff2-cont                     
   (val1 expval?)
   (cont continuation?)
   (try-cont continuation?))
  (unop-arg-cont
   (unop unary-op?)
   (cont continuation?)
   (try-cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)
   (try-cont continuation?))
  (rator-cont          
   (rand expression?)
   (env environment?)
   (cont continuation?)
   (try-cont continuation?))
  (rand-cont                      
   (val1 expval?)
   (cont continuation?)
   (try-cont continuation?))
  (try-cont
   (var symbol?)
   (handler-exp expression?)
   (env environment?)
   (cont continuation?)
   (try-cont continuation?))
  (raise1-cont
   (saved-cont continuation?)
   (try-cont continuation?))
  )


;; value-of-program : Program -> ExpVal
(define value-of-program 
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (value-of/k body (init-env) (end-cont) (end-cont)))))) ;; 首先的try-cont被认为是end-cont

 ;; value-of/k : Exp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env cont a-try-cont)
    ;(eopl:printf "value-of/k :\n exp -> ~a\n\n" exp)
    ;(eopl:printf "value-of/k :\n a-try-cont -> ~a\n\n" a-try-cont)
    (cases expression exp
      
      (const-exp (num) (apply-cont cont (num-val num)))
      
      (const-list-exp (nums)
                      (apply-cont cont
                                  (list-val (map num-val nums))))
      
      (var-exp (var) (apply-cont cont (apply-env env var)))
      
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (diff1-cont exp2 env cont a-try-cont) a-try-cont))
      
      (unop-exp (unop exp1)
                (value-of/k exp1 env
                            (unop-arg-cont unop cont a-try-cont) a-try-cont))
      
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont a-try-cont) a-try-cont))
      
      (proc-exp (var body)
                (eopl:printf "proc-exp :\n var -> ~a\n body -> ~a\n\n" var body)
                (apply-cont cont
                            (proc-val (procedure var body env))))
      
      (call-exp (rator rand)
                (eopl:printf "call-exp :\n rator -> ~a\n rand -> ~a\n a-try-cont -> ~a\n\n" rator rand a-try-cont)
                (value-of/k rator env
                            (rator-cont rand env cont a-try-cont) a-try-cont))
      
      ;; make let a macro, because I'm too lazy to add the extra
      ;; continuation
      (let-exp (var exp1 body)
               ;(eopl:printf "let-exp :\n 将let表达式转换为call表达式 :\n\n ~a <==>\n ~a\n\n" exp (call-exp (proc-exp var body) exp1))
               (value-of/k
                ;; let var = exp1 in body <=> ((proc-exp var body) exp1) 其中exp1是proc(id) exp2的形式
                ;; 好吧，其实这样也是正确的，(var body)确实构成了一个proc-exp，然后exp1相当于参数。
                (call-exp (proc-exp var body) exp1) ;; 好吧，其实这两者是等价的。这里将let表达式转化成为了call表达式。
                env
                cont a-try-cont))
      
      (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of/k
                   letrec-body
                   (extend-env-rec p-name b-var p-body env)
                   cont a-try-cont))
      
      (try-exp (exp1 var handler-exp) ;; 好吧！终于遇到了这个坑货了！
               (eopl:printf "try-exp :\n exp1 -> ~a\n var -> ~a\n handler-exp -> ~a\n\n" exp1 var handler-exp)
               (value-of/k exp1 env
                           (try-cont var handler-exp env cont a-try-cont)
                                     (try-cont var handler-exp env cont a-try-cont) ;; 好吧！这个就是所谓的try-cont
                                     )) ;; 好吧！在try-cont中放入自己
      
      (raise-exp (exp1)
                 (value-of/k exp1 env
                             (raise1-cont cont a-try-cont) a-try-cont)))))

;; apply-cont : continuation * expval -> final-expval
  (define apply-cont
    (lambda (cont val)
      (cases continuation cont
        (end-cont ()
                  (begin
                    (eopl:printf
                     "End of computation.~%")
                    val))
        (diff1-cont (exp2 saved-env saved-cont try-cont)
                    (value-of/k exp2 saved-env (diff2-cont val saved-cont try-cont) try-cont))
        (diff2-cont (val1 saved-cont try-cont)
                    (let ((n1 (expval->num val1))
                          (n2 (expval->num val)))
                      (apply-cont saved-cont
                                  (num-val (- n1 n2)))))
        (unop-arg-cont (unop cont try-cont)
                       (apply-cont cont
                                   (apply-unop unop val)))
        
        (if-test-cont (exp2 exp3 env cont try-cont)
                      (if (expval->bool val)
                          (value-of/k exp2 env cont try-cont)
                          (value-of/k exp3 env cont try-cont)))
        (rator-cont (rand saved-env saved-cont try-cont)
                    ;(eopl:printf "rator计算完成，开始计算rand!\n rator -> ~a\n\n" val)
                    (value-of/k rand saved-env
                                (rand-cont val saved-cont try-cont) try-cont))
        (rand-cont (val1 saved-cont try-cont)
                   ;(eopl:printf "rand计算完成，开始调用函数！\n rand -> ~a\n\n" val)
                   (let ((proc (expval->proc val1)))
                     (apply-procedure proc val saved-cont try-cont)))
        
        ;; the body of the try finished normally-- don't evaluate the handler
        (try-cont (var handler-exp saved-env saved-cont try-cont)
                  (apply-cont saved-cont val))
        ;; val is the value of the argument to raise
        (raise1-cont (saved-cont a-try-cont)
                     ;; we put the short argument first to make the trace more readable.
                     (cases continuation a-try-cont
                       (try-cont (var handler-exp saved-env saved-cont try-cont)
                                 (value-of/k handler-exp
                                             (extend-env var val saved-env)
                                             saved-cont try-cont))
                       (else (report-uncaught-exception))
        )))))

;; apply-procedure : procedure * expval * cont -> final-expval
(define apply-procedure
  (lambda (proc1 arg cont try-cont)
    (cases proc proc1
           (procedure (var body saved-env)
                      (value-of/k body
                                  (extend-env var arg saved-env)
                                  cont try-cont)))))


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
    (expression ("proc" "(" identifier ")" expression)  proc-exp)
    (expression ("(" expression expression ")") call-exp)
    
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    ;; 一谈到异常处理，我还很兴奋呢！
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

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

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
;; 好吧！其实题目并不是很难，但是这个东西调试起来非常艰辛。
;; 这也是动态语言的诟病吧！简单地说一下，在动态语言里面，即使调用函数时给的参数数目不对，这个错误也只能在运行时被发现，很蛋疼的一件事情。
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






