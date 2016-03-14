#lang eopl

(define identifier? symbol?)

;; 这里是出错信息汇总
(define report-expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   A data-structure representation of environments   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; empty-env : () -> Env
(define empty-env
  (lambda () (list 'empty-env)))

;; extend-env : Var * SchemeVal * Env -> Env
(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))
;; apply-env : Env * Var -> Schemeval
(define apply-env
  (lambda (env search-var)
    (cond
      ((eqv? (car env) 'empty-env)
       (report-no-binding-found search-var))
      ((eqv? (car env) 'extend-env)
       (let ((saved-var (cadr env))
             (saved-val (caddr env))
             (saved-env (cadddr env)))
         (if (eqv? search-var saved-var)
             saved-val
             (apply-env saved-env search-var))))
      (else
       (report-invalid-env env)))))
  
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
  
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   sacn&parse                              ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
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
      (expression
        ("-" "(" expression "," expression ")")
        diff-exp)

      (expression
       ("zero?" "(" expression ")")
       zero?-exp)

      (expression
       ("if" expression "then" expression "else" expression)
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" identifier "=" expression "in" expression)
       let-exp)

      ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Syntax data types for the LET language   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-datatype program program?
  (a-program
   (exp1 expressions?)))

(define-datatype expression expressions?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 expressions?)
   (exp2 expressions?))
  (zero?-exp
   (exp1 expressions?))
  (if-exp
   (exp1 expressions?)
   (exp2 expressions?)
   (exp3 expressions?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (expl expressions?)
   (body expressions?))
  (minus ;; 3.6
   (exp1 expressions?))
  (addition ;; 3.7
   (exp1 expressions?)
   (exp2 expressions?))
  (multiplication ;; 3.7
   (exp1 expressions?)
   (exp2 expressions?))
  (div-exp ;; 3.7
   (exp1 expressions?)
   (exp2 expressions?))
  (equal?-exp ;; 3.8
   (exp1 expressions?)
   (exp2 expressions?))
  (greater?-exp ;; 3.8
   (exp1 expressions?)
   (exp2 expressions?))
  (less?-exp ;; 3.8
   (exp1 expressions?)
   (exp2 expressions?))
  (cons-exp ;; 3.9
   (exp1 expressions?)
   (exp2 expressions?))
  (emptylist-exp) ;; 3.9
  (car-exp ;; 3.9
   (exp1 expressions?))
  (cdr-exp ;; 3.9
   (exp1 expressions?))
  (null?-exp ;; 3.9
   (exp1 expressions?))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Expressed values for the LET language   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (pair-val
   (pair pair?))
  (emptylist-val)) ;; 这里稍微需要注意一下的是，添加了一项emptylist-val,不这么干的话，真的不知道要怎样做才行

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

;; expval->list : ExpVal -> List
(define expval->pair
  (lambda (val)
    (cases expval val
      (pair-val (pair) pair)
      (else (report-expval-extractor-error 'pair val)))))

;; expval->car-element : ExpVal -> ExpVal
(define expval->car-element
  (lambda (val)
    (cases expval val
      (pair-val (pair) (car pair))
      (else (report-expval-extractor-error 'pair val)))))

;; expval->cdr-element : ExpVal -> ExpVal
(define expval->cdr-element
  (lambda (val)
    (cases expval val
      (pair-val (pair) (cdr pair))
      (else (report-expval-extractor-error 'pair val)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Interpreter for LET language        ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; value-of-program : Program -> Expval
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
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (minus (exp1) ;; 3.6
             (let ((val1 (value-of exp1 env)))
               (let ((num1 (expval->num val1)))
                 (num-val
                  (- 0 num1)))))
      (addition (exp1 exp2) ;; 3.7
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (+ num1 num2)))))
      (multiplication (exp1 exp2) ;; 3.7
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (* num1 num2)))))
       (div-exp (exp1 exp2) ;; 3.7
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val
                          (/ num1 num2)))))
      (equal?-exp (exp1 exp2) ;; 3.8
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (bool-val (= num1 num2)))))
       (greater?-exp (exp1 exp2) ;; 3.8
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (bool-val (> num1 num2)))))
       (less?-exp (exp1 exp2) ;; 3.8
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (bool-val (< num1 num2)))))
      (cons-exp (exp1 exp2) ;; 3.9
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (pair-val (cons val1 val2))))
      (car-exp (exp1) ;; 3.9
               (let ((val1 (value-of exp1 env)))
                 (expval->car-element val1)))
      (cdr-exp (exp1) ;; 3.9
               (let ((val1 (value-of exp1 env)))
                 (expval->cdr-element val1)))
      (null?-exp (exp1) ;; 3.9
                 (let ((val1 (value-of exp1 env)))
                   (equal? (emptylist-val) val1)))
      (emptylist-exp () (emptylist-val))
                   
                  )))

  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   ex-3.5 ~ ex-3.18                                 ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ex-3.5

;; ex-3.6
;; 扩展语言，添加minus，调用一个参数

;; ex-3.7
;; 扩展语言，添加addition, multiplication,div等特性

;; ex-3.8
;; 扩展语言，添加equal，greater，less等特性

;; ex-3.9
;; 添加list处理过程，包括cons，car，cdr， null和emptylist