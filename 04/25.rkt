#lang eopl
;; Implement multiargument procedures and let expressions.

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
  '((program (statement) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression )"in" expression) let-exp)
    (expression  ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec"  (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("not" "(" expression ")") not-exp)
    ;; statement
    (statement ("{" (separated-list statement ";") "}") block-stat) ;; 块
    (statement ("print" expression) print-stat) ;; 输出state
    (statement (identifier "=" expression) assign-stat)
    (statement ("if" expression statement statement) if-stat)
    (statement ("while" expression statement) while-stat)
    (statement ("var" (separated-list identifier "=" expression ",") ";" statement) declare-stat)
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
  (pair-val
   (car expval?) ;; It's great!
   (cdr expval?))
  (emptylist-val)
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
	   (a-program (stat1)
                      (begin
                        (set! global-env (init-env))
                        (let [(res  (value-of-stat stat1))]
                          (begin
                            (set! global-env (init-env)) ;; 这段代码运行完成之后要将global-env清空
                            res
                       )))))))

(define global-env 'uintialized) ;; 这里定义一个全局的env

(define value-of-stat
  (lambda (stat) ;; 
    (cases statement stat
      (print-stat (exp1) ;; 好吧,这个语句解析得不错
                  (let [(res (value-of exp1 global-env))]
                    (begin
                      (display res)
                      (newline))))
      (assign-stat (var exp1) ;; 好吧,这个语句解析得也还好
                   (let [(val (value-of exp1 global-env))]
                     (begin
                       ;(print "assign-stat value-of-stat var -> " var)
                       ;(print "assign-stat value-of-stat val -> " val)
                       (apply-env global-env var) ;; 首先要在env中找到该变量才行
                       (set! global-env (extend-env var (newref val) global-env))
                       ;(print "global-env -> " global-env)
                       ))) ;; 这个玩意要连续不断地变才行
      (block-stat (blist) ;; 这个语句解析得也正确
                  (begin
                    ;(print "现在开始,要顺序执行state语句啦!" blist)
                    (letrec [(top-down-run
                           (lambda (alist)
                             (if (null? alist)
                                 (num-val 0) ;; 成功执行完毕返回0
                                 (begin
                                   (value-of-stat (car alist))
                                   (top-down-run (cdr alist))))))]
                      (top-down-run blist))))
      (if-stat (exp1 stat1 stat2) ;; 解析得其实也还好
               (if (expval->bool (value-of exp1 global-env))
                   (value-of-stat stat1)
                   (value-of-stat stat2)))
      (while-stat (exp1 stat1) ;; 解析while语句其实还是挺有趣的
                  (begin
                    ;(print "while-stat exp1 -> " exp1)
                    ;(print "while-stat stat1 -> " stat1)
                    (letrec [(interpreter-while
                              (lambda ()
                                (if (expval->bool (value-of exp1 global-env))
                                    (begin
                                      (value-of-stat stat1)
                                      (interpreter-while))
                                    (num-val 1))))]
                      (interpreter-while))))
      (declare-stat (var-list exp-list stat1)
                    (begin
                      (let [(backup global-env)
                            (val-list (map (lambda (x) (value-of x global-env)) exp-list))] ;; 先备份起来
                        (begin
                          (extend-env-with-var-and-val-list var-list val-list)
                      ;(print "declare-stat global-env -> " global-env)
                          (value-of-stat stat1)
                          (set! global-env backup)))))
                               
      
      (else (eopl:error "value-of-state dismatch!")))))
(define (extend-env-with-var-and-val-list var-list val-list)
  (if (null? var-list)
      (num-val 0)
      (begin
        (set! global-env (extend-env (car var-list) (newref (car val-list)) global-env)) ;; -1 代表只是声明了变量,而没有初始化
        (extend-env-with-var-and-val-list (cdr var-list) (cdr val-list)))))

(define (extend-env-with-var-list varlist)
  (if (null? varlist)
      (num-val 0)
      (begin
        (set! global-env (extend-env (car varlist) -1 global-env)) ;; -1 代表只是声明了变量,而没有初始化
        (extend-env-with-var-list (cdr varlist)))))

;; value-of : Exp * Env -> ExpVal
;; Page: 113
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var))) ;; var实际存储的是指针一类的东西,通过解引用(deref)才能获得正确的值
      
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
      (not-exp (exp1)
               (let [(val (value-of exp1 env))]
                   (if (expval->bool val)
                       (bool-val #f)
                       (bool-val #t))))
      
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      
      (let-exp (var-list exp-list body)
               (begin
                 (print "value-of let-exp var-list --> " var-list)
                 (print "value-of let-exp exp-list --> " exp-list)
                 (let ((val-list (map (lambda (x) (value-of x env)) exp-list)))
                   (value-of body
                             (extend-env-list var-list val-list env))
                   )))
      
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (map (lambda (x) (value-of x env)) rand)))
                  (begin
                    ;(print "value-of call-exp arg -> " arg)
                    ;(print "value-of call-exp proc -> " proc)
                    (apply-procedure proc arg))))
      
      (letrec-exp (p-names b-vars-list p-bodies letrec-body)
                  (begin
                   ;(print "valueof letrec-exp b-vars-list -->" b-vars-list)
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
      (list-exp (alist)
                (if (null? alist) (emptylist-val)
                    (pair-val
                     (value-of (car alist) env)
                     (value-of (list-exp (cdr alist)) env))))
      (car-exp (body)
               (expval->car (value-of body env)))
      (cdr-exp (body)
               (expval->cdr (value-of body env)))
      (null?-exp (exp)
                 (expval->null? (value-of exp env)))
      (emptylist-exp () (emptylist-val)) ;;
      (cons-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (pair-val val1 val2)))
      (assign-exp (var exp1)
                  (begin
                    (setref!
                     (apply-env env var)
                     (value-of exp1 env))
                    (num-val 27)))
      
      (else (eopl:error "bad match"))
                  
      )))

;; instrumented version
(define apply-procedure
  (lambda (proc1 val-list)
    (cases proc proc1
	   (procedure (var-list body saved-env) ;; var表示变量名
                      (begin
                        ;(print "apply-procedure var-list -> " var-list)
                         ;(print "apply-procedure val-list -> " val-list)
                         ;(print "extend-env-list res -> " (extend-env-list var-list val-list saved-env))
                        (value-of body (extend-env-list var-list val-list saved-env)))))))

(define (extend-env-list var-list val-list env)
  (if (null? var-list) env
      (extend-env-list (cdr var-list) (cdr val-list) (extend-env (car var-list) (newref (car val-list)) env)))) 



(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code

(run "var x = 1, y = 3; {print x; print y}")


