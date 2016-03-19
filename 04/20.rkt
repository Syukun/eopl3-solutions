#lang eopl
;; Extend the language 

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

    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("null?" "(" expression ")") null?-exp)

    ;; assign
    (expression ("set" identifier "=" expression) assign-exp)
    (expression
     ("letmutable" (arbno identifier "=" expression) "in" expression)
     letmutable-exp)
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
   (bmutable boolean?) ;; bmutable这个域指示该变量是否可变
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
  (lambda (env search-var bmodify) ;; bmodify是一个bool量，表示是否修改
    (cases environment env
           (empty-env ()
                      (eopl:error 'apply-env "No binding for ~s" search-var))
           (extend-env (bmutable bvar bval saved-env)
                       (if (eqv? search-var bvar)
                           (if bmodify ;; 如果要求更改该变量
                               (if bmutable ;; 并且该变量是能够修改的
                                   bval
                                   (eopl:error search-var "can't be modified!")) ;; 表示该变量不能够被修改
                               bval) ;;即使不要求修改这个变量，也要返回对应的值
                           (apply-env saved-env search-var bmodify)))
           (extend-env-rec* (p-names b-vars p-bodies saved-env)
                            (cond
                             ((location search-var p-names) ;; 查找函数名
                              => (lambda (n) ;; 如果前面的location函数返回了一个数
                                   (newref ;; 构造一个引用
                                    (proc-val ;; 构造出一个函数
                                     (procedure
                                      (list-ref b-vars n) ;; 我没有看错吧,居然直接调用list的函数来取形式参数
                                      (list-ref p-bodies n) ;; 和对应的函数体
                                      env)))))
                             (else (apply-env saved-env search-var bmodify)))))))

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
      ;; 不要求修改var指向的东西，所以apply-env的bmodify设置为false
      (var-exp (var) (deref (apply-env env var #f))) ;; var实际存储的是指针一类的东西,通过解引用(deref)才能获得正确的值
      
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
                 (print "value-of let-exp var-list --> " var-list)
                 (print "value-of let-exp exp-list --> " exp-list)
                 (let ((val-list (map (lambda (x) (value-of x env)) exp-list)))
                   (value-of body
                             (extend-env-with-immutable-var-list var-list val-list env)) ;; let语句里的变量是不可变的 
                   )))
      (letmutable-exp (var-list exp-list body)
                      (let ((val-list (map (lambda (x) (value-of x env)) exp-list)))
                        (value-of body
                                  (extend-env-with-muatble-var-list var-list val-list env)) ;; letmutable语句里的变量是可变的
                        ))    
      
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (map (lambda (x) (value-of x env)) rand)))
                  (begin
                    (print "value-of call-exp arg -> " arg)
                    (print "value-of call-exp proc -> " proc)
                    (apply-procedure proc arg))))
      
      (letrec-exp (p-names b-vars-list p-bodies letrec-body)
                  (begin
                    (print "valueof letrec-exp b-vars-list -->" b-vars-list)
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
                     (apply-env env var #t) ;; 要求修改变量的值，当然，只有可变的变量才是可以修改的。
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
                        (print "apply-procedure var-list -> " var-list)
                        (print "apply-procedure body -> " body)
                        (print "apply-procedure val-list -> " val-list)
                        (value-of body (extend-env-with-immutable-var-list var-list val-list saved-env)))))))

;; 不可变的variable
(define (extend-env-with-immutable-var-list var-list val-list env)
  (if (null? var-list) env
      (extend-env-with-immutable-var-list
       (cdr var-list)
       (cdr val-list)
       (extend-env  #f (car var-list)
                    (newref (car val-list)) env)))) ;; 不可变的变量在env中直接map到对应的值

;; 可变的variable
(define (extend-env-with-muatble-var-list var-list val-list env)
  (if (null? var-list) env
      (extend-env-with-muatble-var-list
       (cdr var-list)
       (cdr val-list)
       (extend-env #t (car var-list)
                   (newref (car val-list)) env)))) ;; 可变的变量在env中map到对应的值的引用

;;


(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code
(run
 "letmutable x = 4 in
        begin
        set x = 5;
        -(1, x) end")
(run
 "let x = 4 in begin
               set x = 5;
               -(1, x) end")

