#lang eopl
(require "scheduler.rkt")
(require "store.rkt")
(require "queue.rkt")
(define trace #f)
;; 实现一个用date-structure表述的thread

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
   (rand expression?) 
   (env environment?)
   (cont continuation?))
  
   (rand-cont
    (val1 expval?)
    (cont continuation?))
  
  (try-cont
   (var symbol?)
   (handler-exp expression?)
   (env environment?)
   (cont continuation?))
  
  (raise1-cont
   (saved-cont continuation?))

  (end-main-thread-cont)
  (end-subthread-cont)
  
  (spawn-cont
   (saved-cont continuation?))
  
  (set-rhs-cont
   (loc reference?)
   (cont continuation?))

  (wait-cont
   (saved-cont continuation?))
  (signal-cont
   (saved-cont continuation?))
  )

;; value-of-program : Program -> ExpVal
(define value-of-program 
  (lambda (timeslice pgm)
    (initialize-store!)
    (initialize-scheduler! timeslice) ;; 初始化最大的时间片
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (end-main-thread-cont))))))

;; value-of/k : Exp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      
      (const-exp (num) (apply-cont cont (num-val num)))
      
      (const-list-exp (nums)
                      (if trace (eopl:printf "const-list-exp :\n nums -> ~a\n cont -> ~a \n\n" nums cont) #f)
                      (apply-cont cont
                                  (list-val (map num-val nums))))
      
      (var-exp (var)
               (apply-cont cont (deref (apply-env env var))))
      
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (diff1-cont exp2 env cont)))
      
      (unop-exp (unop exp1)
                (value-of/k exp1 env
                            (unop-arg-cont unop cont)))
      
      (if-exp (exp1 exp2 exp3)
              (if trace (eopl:printf "if-exp :\n exp1 -> ~a\n exp2 -> ~a\n exp3 -> ~a\n\n" exp1 exp2 exp3) #f)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont)))
      ;; 好吧,要开始改变这里的东西啦!
      (proc-exp (var body)
                (apply-cont cont
                            (proc-val (procedure var body env))))
      
      (call-exp (rator rand)
                (if trace (eopl:printf "call-exp :\n rator -> ~a\n rand -> ~a\n\n" rator rand) #f)
                (value-of/k rator env
                            (rator-cont rand env cont)))
      
      (let-exp (var exp1 body) 
               (value-of/k
                (call-exp (proc-exp var body) exp1) 
                env
                cont))
      
      (letrec-exp (p-name b-var p-body letrec-body)
                  (if trace (eopl:printf "letrec-exp :\n p-body -> ~a\n\n" p-body) #f)
                  (value-of/k
                   letrec-body
                   (extend-env-rec p-name b-var p-body env)
                   cont))
      
      (try-exp (exp1 var handler-exp)
               (value-of/k exp1 env
                           (try-cont var handler-exp env cont)))
      
      (raise-exp (exp1)
                 (value-of/k exp1 env
                             (raise1-cont cont)))
      
      (spawn-exp (exp) ;; 好吧!所谓的spawn-exp
                 (value-of/k exp env
                             (spawn-cont cont)))
      (begin-exp (exp exps)
                 (if trace
                     (eopl:printf "begin-exp :\n exp -> ~a\n exps -> ~a\n\n" exp exps)
                     #f)
                 (if (null? exps)
                     (value-of/k exp env cont)
                     (value-of/k (call-exp (proc-exp (fresh-identifier 'dummy)
                                                     (begin-exp (car exps) (cdr exps)))
                                           exp) env cont)))

      (set-exp (id exp)
               (value-of/k exp env
                           (set-rhs-cont (apply-env env id) cont)))

      ;; about mutex
      (mutex-exp ()
             (apply-cont cont (mutex-val (new-mutex))))
      (wait-exp (exp)
                (value-of/k exp env (wait-cont cont)))
      (signal-exp (exp)
                  (value-of/k exp env (signal-cont cont)))
      
      )))

;; 好吧!很新奇的一个小玩意。主要干了什么呢,没干嘛,生成不重复的字符
(define fresh-identifier
  (let [(sn 0)]
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append (symbol->string identifier) "%" (number->string sn))))))

;; apply-cont : continuation * expval -> final-expval
(define apply-cont
  (lambda (cont val)
    (if (time-expired?) 
        (begin ;; 如果时间片到了
          (place-on-ready-queue!
           (lambda () (apply-cont cont val))) ;; 将这个玩意包裹起来
          (run-next-thread)) ;; 转而运行下一个thread
        (begin
          (decrement-timer!) ;; 否则时间片减一,继续执行
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
           ;; 错误居然出现在了这里,真是够神奇的啦!
            (unop-arg-cont (unop cont)
                           (apply-unop unop val cont))
            
            (if-test-cont (exp2 exp3 env cont)
                          (if trace (eopl:printf "if-test-cont :\n val -> ~a exp3 -> ~a\n\n" val exp3) #f)
                          (if (expval->bool val)
                              (value-of/k exp2 env cont)
                              (value-of/k exp3 env cont)))
            ;; new-stuff
            (rator-cont (rand saved-env saved-cont)
                        ;(eopl:printf "rator-cont : val -> ~a\n" val)
                        (value-of/k rand saved-env
                                    (rand-cont val saved-cont)))
            
            (rand-cont (val1 saved-cont)
                       (if trace (eopl:printf "rand-cont :\n val1 -> ~a\n val -> ~a\n\n" val1 val) #f)
                       (let [(proc1 (expval->proc val1))]
                         (apply-procedure proc1 val saved-cont)))
            
            (try-cont (var handler-exp saved-env saved-cont)
                      (apply-cont saved-cont val))
            
            (raise1-cont (saved-cont)
                         (apply-handler val saved-cont))
            
            (end-main-thread-cont ()
                                  (set-final-answer! val)
                                  (run-next-thread))
            (end-subthread-cont ()
                                (run-next-thread))
            (spawn-cont (saved-cont)
                        (let [(proc1 (expval->proc val))]
                          (place-on-ready-queue!
                           (lambda ()
                             (apply-procedure proc1
                                              (num-val 28)
                                              (end-subthread-cont))))
                          (apply-cont saved-cont (num-val 73))))
            (set-rhs-cont (loc cont)
                          (begin
                            (setref! loc val)
                            (apply-cont cont (num-val 26)))) ;;返回的值是26

            (wait-cont (saved-cont)
                       (wait-for-mutex
                        (expval->mutex val)
                        (lambda () (apply-cont saved-cont (num-val 52)))))
            (signal-cont (saved-cont)
                         (signal-mutex
                          (expval->mutex val)
                          (lambda () (apply-cont saved-cont (num-val 53)))))
      
      )))))

(define apply-procedure
  (lambda (proc1 arg cont)
    (cases proc proc1
           (procedure (var body saved-env)
                      (if trace (eopl:printf "apply-procedure :\n var -> ~a\n body -> ~a\n\n" var body) #f)
                      (value-of/k body
                                  (extend-env var (newref arg) saved-env)
                                  cont)))))

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
                               (newref (proc-val (procedure b-var p-body env)))
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
    ;; 一谈到异常处理,我还很兴奋呢!
    (expression ("try" expression "catch" "(" identifier ")" expression) try-exp)
    (expression ("raise" expression) raise-exp)
    (expression (unary-op "(" expression ")") unop-exp) ;; 这个unary-op非常有意思
    (unary-op ("null?") null?-unop)
    (unary-op ("car") car-unop)
    (unary-op ("cdr") cdr-unop)
    (unary-op ("zero?") zero?-unop)
    (unary-op ("print") print-unop)
    ;; Lists. We will have lists of literal number only.
   ; (expression ("list" "(" (separated-list number ",") ")") const-list-exp)
    (expression ("[" (separated-list number ",") "]") const-list-exp)
    (expression ("spawn" "(" expression ")") spawn-exp) ;; spawn
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("set" identifier "=" expression) set-exp)
    (expression ("signal" "(" expression ")") signal-exp)
    (expression ("wait" "(" expression ")" ) wait-exp)
    (expression ("mutex" "(" ")") mutex-exp)
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
  (mutex-val
   (mut mutex?))
   )

;;; extractors
(define expval->mutex
  (lambda (v)
    (cases expval v
      (mutex-val (mut) mut)
      (else (expval-extractor-error 'mutex v)))))

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
   (bvar symbol?)
   (body expression?)
   (env environment?)))

;;;;;;;;;;;;;;;; environment structures ;;;;;;;;;;;;;;;;
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval reference?)
   (saved-env environment?))
  (extend-env-rec
   (p-name symbol?)
   (b-var symbol?)
   (p-body expression?)
   (saved-env environment?)))

(define init-env
  (lambda ()
    (empty-env)))

(define run
  (lambda (timeslice string)
    (value-of-program timeslice (scan&parse string))))

(define apply-handler
  (lambda (val cont)
    (cases continuation cont
     ;; interesting cases
      (try-cont (var handler-exp saved-env saved-cont)
                (value-of/k handler-exp
                            (extend-env var (newref val) saved-env)
                            saved-cont))
      (end-main-thread-cont () (report-uncaught-exception))
      (end-subthread-cont () (report-uncaught-exception))
      (spawn-cont (saved-cont) (apply-handler val saved-cont))
      (end-cont ()
                (report-uncaught-exception)) ;; 未被捕获到的异常
      (set-rhs-cont (loc saved-cont)
                     (apply-handler val saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (apply-handler val saved-cont))
      (diff1-cont (exp2 saved-env saved-cont)
                  (apply-handler val saved-cont))
      (diff2-cont (val1 saved-cont)
                  (apply-handler val saved-cont))
      (rator-cont (rand saved-env saved-cont)
                  (apply-handler val saved-cont))
      (rand-cont (val1 saved-cont)
                 (apply-handler val saved-cont))
      (raise1-cont (cont)
                   (apply-handler val cont))
      (unop-arg-cont (unop saved-cont)
                     (apply-handler val saved-cont))
      (signal-cont (saved-cont)
                  (apply-handler val saved-cont))
      (wait-cont (saved-cont)
                 (apply-handler val saved-cont))
      )))

(define report-uncaught-exception
  (lambda ()
    (eopl:error 'apply-handler "uncaught exception!")))

(define apply-unop
  (lambda (unop val cont)
    (cases unary-op unop
      (null?-unop ()
                  (if trace (eopl:printf "null?-unop :\n\n ") #f)
                  (apply-cont cont (bool-val (null? (expval->list val)))))
      (car-unop ()
                (apply-cont cont (car (expval->list val))))
      (cdr-unop ()
                (apply-cont cont (list-val (cdr (expval->list val)))))
      (zero?-unop ()
                  (apply-cont cont (bool-val (zero? (expval->num val)))))

      (print-unop ()
                  (begin
                    (eopl:printf "~a\n" (expval->num val))
                    (apply-cont cont (num-val 1)))) ;; 返回值为1
      )))

;; 好吧!新的类型
(define-datatype mutex mutex?
  (a-mutex
   (ref-to-closed? reference?)
   (ref-to-wait-queue reference?)))

;; 新创建一个mutex
(define new-mutex
  (lambda ()
    (a-mutex
     (newref #f) ;; ref-to-closed? 
     (newref '()))))

;; wait-for-mutex : Mutex * Thread -> FinalAnswer
(define wait-for-mutex
  (lambda (m th) ;; th代表thread
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
               (cond
                 [(deref ref-to-closed?) (setref! ref-to-wait-queue
                                                  (enqueue (deref ref-to-wait-queue) th))
                                         (run-next-thread)]
                 [else (setref! ref-to-closed? #t)
                       (th)])))))

;; signal-mutex : Mutex * Thread -> FinalAnswer
(define signal-mutex
  (lambda (m th) ;; m指的是mutex
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
               (let [(closed? (deref ref-to-closed?))
                     (wait-queue (deref ref-to-wait-queue))]
                 (if closed? ;; 如果mutex被关闭了
                     (if (empty? wait-queue) 
                         (setref! ref-to-closed? #f) ;; 等待队列为空, 释放mutex
                         (dequeue wait-queue
                                  (lambda (first-waiting-th other-waiting-ths)
                                    (place-on-ready-queue!
                                     first-waiting-th) ;; 从等待队列里面取出thread,放在就绪队列上
                                    (setref!
                                     ref-to-wait-queue
                                     other-waiting-ths)))) #f)
                 (th)))))) ;; 如果mutex没有被关闭的话,继续运行原来的线程

(define-datatype thread thread?
  (a-thread
   (saved-val expval?) 
   (saved-cont continuation?) ;; 保存的continuation
   (saved-time integer?))) ;; 剩余的时间片

;; test code











