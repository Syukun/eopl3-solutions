#lang eopl
;; Add a lazy let to the call-by-need interpreter.

(require "./base/store.rkt")
(require "./base/helper.rkt")

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;
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

    (expression ("let" (arbno identifier "=" expression )"in" expression) let-exp)

    (expression  ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)

    (expression ("(" expression (arbno expression) ")") call-exp)

    (expression ("letrec"  (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)

    ;; new stuff
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)

    (expression ("newref" "(" expression ")") newref-exp)

    (expression ("deref" "(" expression ")") deref-exp)

    (expression ("setref" "(" expression "," expression ")") setref-exp)

    ;; assign
    (expression ("set" identifier "=" expression) assign-exp)
    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))


;;; an expressed value is either a number, a boolean, a procval, or a
;;; reference.
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (ref-val ;; 引用类型
   (ref reference?))
  )

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

(define expval->ref
  (lambda (v)
    (cases expval v
	   (ref-val (ref) ref)
	   (else (expval-extractor-error 'reference v)))))
         
(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
		variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

(define-datatype proc proc? ;; 函数类型
  (procedure
   (bvar (list-of symbol?))
   (body expression?)
   (env environment?)))

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval reference?)
   (saved-env environment?))
  (extend-env-rec*
   (proc-names (list-of symbol?)) ;; 好吧,不得不说,这个玩意还是很厉害的。
   (b-vars (list-of (list-of symbol?))) ;; 扩展的特性,支持多重参数
   (proc-bodies (list-of expression?))
   (saved-env environment?)))

(define init-env
  (lambda ()
    (empty-env)))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;
(define apply-env
  (lambda (env search-sym)
    (cases environment env
           (empty-env ()
                      (eopl:error 'apply-env "No binding for ~s" search-sym))
           (extend-env (bvar bval saved-env)
                       (if (eqv? search-sym bvar)
                           bval
                           (apply-env saved-env search-sym)))
           (extend-env-rec* (p-names b-vars p-bodies saved-env)
                            (cond
                             ((location search-sym p-names) ;; 查找函数名
                              => (lambda (n) ;; 如果前面的location函数返回了一个数
                                   (newref ;; 构造一个引用
                                    (proc-val ;; 构造出一个函数
                                     (procedure
                                      (list-ref b-vars n) ;; 我没有看错吧,居然直接调用list的函数来取形式参数
                                      (list-ref p-bodies n) ;; 和对应的函数体
                                      env)))))
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


;; value-of-program : Program -> ExpVal
;; Page: 110
(define value-of-program
  (lambda (pgm)
    (initialize-store!)               ; new for explicit refs.
    (cases program pgm
	   (a-program (exp1)
		      (value-of exp1 (init-env))))))

;; value-of : Exp * Env -> ExpVal
;; Page: 113
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      
      ;; call-by-need
      (var-exp (var)
               (let ((ref1 (apply-env env var)))
                 (let ((w (deref ref1)))
                   (begin
                     ;(print "ref1 -> " ref1)
                     ;(print "w -> " w)
                     (if (expval? w) ;; 如果已经是值了,直接返回这个值,否则要计算thunk
                         w
                         (let ((val1 (value-of-thunk w)))
                           (begin
                             (setref! ref1 val1)
                             val1)))))))
      
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      
      (let-exp (var-list exp-list body)
               (begin
                 ;(print "let-exp var-list -> " var-list)
                 ;(print "let-exp exp-list -> " exp-list)
                 ;(print "let-exp body -> " body)
                 (let ((val-list (map (lambda (x) (value-of-oprand x env)) exp-list))) ;; 好吧，此时的val，都是thunk
                   (begin
                     ;(print "let-exp val-list -> " val-list)
                     ;(print "deref 0 -> " (deref 0))
                     ;(print "let-exp body -> " body)
                     (value-of body
                               (extend-env-list var-list val-list env)))
                     )))
      
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      
      (call-exp (rator rand)
                (begin
                  ;(print "call-exp rator -> " rator)
                  (let ((proc (expval->proc (value-of rator env))) ;; 抽取出procedure
                        (arg (map (lambda (x) (value-of-oprand x env)) rand)))
                    (begin
                      ;(print "valueof call-exp rator -> " rator) 
                      ;(print "valueof call-exp proc -> " proc) 
                      ;(print "valueof call-exp arg -> " arg) 
                      (apply-procedure proc arg)))))
      
      (letrec-exp (p-names b-vars-list p-bodies letrec-body)
                  (begin
                    ;(print "valueof letrec-exp b-vars-list ->" b-vars-list)
                    (value-of letrec-body
                              (extend-env-rec* p-names b-vars-list p-bodies env))))
      
      (begin-exp (exp1 exps) ;; 这个式子只做了一件事情,从左至右执行begin的各个语句,最后将最后的语句的执行结果返回
                 (letrec
                     ((value-of-begins
                       (lambda (e1 es)
                         (let ((v1 (value-of e1 env)))
                           (if (null? es)
                               v1
                               (value-of-begins (car es) (cdr es)))))))
                   (value-of-begins exp1 exps)))
      
      (newref-exp (exp1)
                  (let ((v1 (value-of exp1 env)))
                    (ref-val (newref v1)))) ;; 返回引用值
      
      (deref-exp (exp1)
                 (let ((v1 (value-of exp1 env)))
                   (let ((ref1 (expval->ref v1)))
                     (deref ref1))))
      
      (setref-exp (exp1 exp2)
                  (let ((ref1 (expval->ref (value-of exp1 env)))
                        (v2 (value-of exp2 env)))
                    (begin
                      (setref! ref1 v2)
                      (num-val 23))))
     
      (assign-exp (var exp1)
                  (begin
                    (setref!
                     (apply-env env var)
                     (value-of exp1 env))
                    (num-val 27)))
      (else (eopl:error "bad match"))
                  
      )))

;; new type thunk
(define-datatype thunk thunk?
  (a-thunk
   (exp1 expression?)
   (env environment?)))
;; new stuff
;; value-of-oprand : Exp * Env -> ref
;; 如果exp表达式是一个var-exp那么返回该变量对应的引用,否则的话,返回该值
(define value-of-oprand
  (lambda (exp env)
    (cases expression exp
      (var-exp (var) (apply-env env var)) ;; 直接从env中搜寻出ref
      (const-exp (c) (newref (value-of exp env))) ;; 常数和procedure不创建thunk
      (proc-exp (var body) (newref (value-of exp env)))
      (else
       (newref (a-thunk exp env)))))) ;; 构建一个thunk

;; value-of-thunk : Thunk -> ExpVal
(define value-of-thunk
  (lambda (th)
    (cases thunk th
      (a-thunk (exp1 saved-env)
               (value-of exp1 saved-env)))))


;; instrumented version
(define apply-procedure
  (lambda (proc1 val-list)
    (cases proc proc1
	   (procedure (var-list body saved-env) ;; var表示变量名
                      (begin
                        ;(print "apply-procedure val-list -> " val-list)
                        (value-of body (extend-env-list var-list val-list saved-env)))))))

(define (extend-env-list var-list val-list env)
  (if (null? var-list) env
      (extend-env-list (cdr var-list)
                       (cdr val-list)
                       (extend-env (car var-list) (car val-list) env)))) 

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code
(run "letrec loop (x) = (loop -(x, 1)) in let f = proc (z) 11 in (f (loop 10))")




