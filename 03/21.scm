(load-relative "../libs/init.scm")
(load-relative "./base/environments.scm")

;; ex-21
;; extend the language to include procedures with multiple arguments and calls with multiple operands.

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
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ;;new stuff
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
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
  ;;new stuff
  (let-proc-exp
   (proc-name identifier?)
   (proc-args identifier?)
   (proc-body expression?)
   (let-body expression?))
  (proc-exp
   (proc-args (list-of identifier?)) ;; Arguments are a list of identifier.
   (proc-body expression?)) ;; I guess that it will have a problem!
  (call-exp
   (rator expression?)
   (rand expression?)))


;;; an expressed value is either a number, a boolean or a procval.
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?)))

;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (var list?) ;;multiple arguments
   (body expression?) ;; function body
   (env environment?))) ;; closure


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
;; Page: 79
(define apply-procedure ;; this is a very important procudure, it calls the procedure we defined.
  (lambda (proc1 args-list)
    (cases proc proc1
           (procedure (var-list body saved-env)
                      (value-of body (binding-args var-list args-list saved-env saved-env))
		      ;;saved-env
		      ))))

;; binding-args
(define (binding-args var-list val-list old-env new-env)
  (if (null? var-list)
      new-env
      (binding-args (cdr var-list)
		    (cdr val-list)
		    old-env
		    (extend-env (car var-list)
				(car val-list)
				new-env))))
;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;
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
	   ;;new stuff
	   (proc-exp (proc-arg proc-body)
			  (proc-val (procedure proc-arg proc-body env)))
	   
	   (let-proc-exp (proc-name proc-args proc-body let-body)
		    (let ((proc (proc-val (procedure proc-args proc-body env)))) ;;get the 
		      (value-of let-body
				(extend-env proc-name proc env))))
	   (call-exp (rator rand)
		     (begin
		      ;; (print (expval->proc (value-of rator env)))
		      ;; (print (map (apply-elem env) rand))
		       (let ((proc (expval->proc (value-of rator env)))
			     (arg (map (apply-elem env) rand)))
			 (apply-procedure proc arg))))
	   )))

;; apply-elem 
(define (apply-elem env)
  (lambda (val)
    (value-of val env)))

;; run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test
(run "let f = proc (x, y, z) -(x, -(z, y)) in (f 3 4 5)")

