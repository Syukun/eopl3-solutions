(load-relative "../libs/init.scm")
;; ex-33
;; Support mutually recursive procedures, each of possibly many arguments.


;;;;;;;;;ectend-env-rec;;;;;;;;;;;
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))
  (extend-env-rec
   (p-name (list-of identifier?))
   (b-var (list-of (list-of identifier?)))
   (body (list-of expression?))
   (env environment?)))

;; now we see the power of abstract interface
;; even though we change the implement of the environment, as long as we provide the same interface, everything is ok.
(define apply-env
  (lambda (env search-var)
    (begin
      (print "apply-env : env --> " env)
      (print "apply-env : search-var --> " search-var)
      (cases environment env
	     [empty-env () (error 'apply-env "No binding for ~s" search-var)]
	     [extend-env (saved-var saved-val saved-env)
			 (if (eqv? saved-var search-var)
			     saved-val
			     (apply-env saved-env search-var))]
	     [extend-env-rec (p-names b-vars p-bodies saved-env)
			     (begin
			       (print "apply-env : p-names --> " p-names)
			       (print "apply-env : b-vars --> " b-vars)
			       (print "apply-env : p-bodies --> " p-bodies)
			       (print "apply-env : saved-env --> " saved-env)
			       (if (null? p-names)
				   (apply-env saved-env search-var)
				   (let [(res (equal-name? search-var p-names b-vars p-bodies))]
				     (begin
				       (print "apply-env : res --> " res)
				       (if (car res)
					   (begin
					     (let [(a-proc-val (proc-val (procedure (cadr res) (caddr res) env)))]
					       (print "apply-env : a-proc-val --> " a-proc-val)
					       a-proc-val))
					   (apply-env saved-env search-var)
					   )))))]))))


(define (equal-name? search-name nlist vlist blist)
  (cond
   [(null? nlist) (list #f)]
   [(eqv? search-name (car nlist)) (list #t (car vlist) (car blist))]
   [else (equal-name?  search-name (cdr nlist) (cdr vlist) (cdr blist))]))


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
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression )
                 "in" expression) letrec-exp)
    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;; datetype ;;;
(define-datatype expression expression?
  (var-exp
   (id symbol?))
  (const-exp
   (num number?))
  (zero?-exp
   (expr expression?))
  (if-exp
   (predicate-exp expression?)
   (true-exp expression?)
   (false-exp expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  ;; new-stuff
  (letrec-exp
   (names (list-of identifier?)) ;; procedure names list
   (vars (list-of (list-of identifier?))) ;;Note: variable list
   (bodies (list-of expression?)) ;; code body
   (body (expression?))) ;; What we need to excute
  )


;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (var (list-of symbol?)) ;; now our let-language support multiple argments.
   (body expression?)
   (env environment?)
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
    (cases expval v
           (num-val (num) num)
           (else (expval-extractor-error 'num v)))))

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
    (error 'expval-extractors "Looking for a ~s, found ~s"
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
			  (print "apply-procedure : new-env --> " (extend-env-list var val saved-env))
			  (value-of body (extend-env-list var val saved-env))))
	     ))))

(define (extend-env-list varlist vallist env)
  (if (null? varlist)
      env
      (extend-env-list (cdr varlist)
		       (cdr vallist)
		       (extend-env (car varlist)
				   (car vallist)
				   env))))
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
	   (letrec-exp (names vars bodies body)
		       (begin
			 (print "letrec-exp : names --> " names)
			 (print "letrec-exp : vars --> " vars)
			 (print "letrec-exp : bodies --> " bodies)
			 (print "letrec-exp : body --> " body)
			 (print "letrec-exp : env --> " env)
			 (let [(new-env (extend-env-rec names vars bodies env))]
			   (begin
			     (print "letrec-exp : new-env --> " new-env)
			     (print (value-of body new-env))
			     (value-of body new-env)))
			 )) 
           (proc-exp (var body)
		     (begin
		       ;(print "proc-exp : var --> " var) 
		       ;(print "proc-exp : body --> " body)
		       ;(procedure var body env)
		       (proc-val (procedure var body env))
		       )) 
	   (call-exp (rator rand)
		     (begin
		       (print "call-exp : rand --> " rand)
		       (print "call-exp : (expval->proc (value-of rator env)) --> " (expval->proc (value-of rator env)))
		       (print "call-exp : (value-of rand env) --> "  (map (lambda (x) (value-of x env)) rand))
		       (let ((proc (expval->proc (value-of rator env)))
			     (args (map (lambda (x) (value-of x env)) rand)))
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

;; test-code
 (run "letrec g (x, y, z) = if zero?(x) then 1 else (f x z)  f(x, y) = -(x, y) in (g 1 2 3)")
