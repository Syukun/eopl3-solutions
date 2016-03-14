(load-relative "../libs/init.scm")
(load-relative "./base/environments.scm")

;; ex-25
;; Modify the representation of procedures to retain only the free variables.

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
    (expression ("*" "(" expression "," expression ")") mult-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ;;new stuff
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
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
   (vars symbol?)
   (vals expression?)
   (body expression?))
  ;;new stuff
  (mult-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-proc-exp
   (proc-name identifier?)
   (proc-args identifier?)
   (proc-body expression?)
   (let-body expression?))
  (proc-exp
   (proc-name identifier?)
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
   (var symbol?) ;; arguments
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
  (lambda (proc1 val)
    (cases proc proc1
           (procedure (var body saved-env)
                      (value-of body (extend-env var val saved-env))))))

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
		    (begin
		      (let [(val1 (value-of exp1 env))]
			(value-of body
				  (extend-env var val1 env)))))
	   ;;new stuff
	   (mult-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val
                          (* num1 num2)))))
	   (proc-exp (proc-arg proc-body) ;; We should extract the free variables in the environment.
		     (begin
		      ; (print "-------------------enter--proc-exp-")
		      ; (print proc-arg)
		      ; (print proc-body)
		      ; (print "proc-exp -->" exp)
		      ; (print "env -->" env)
		       (begin
			; (print vlist)
			; (print new-env)
			 (proc-val (procedure proc-arg
					      proc-body
					      (gen-new-env (remove-dup exp)
							   env))))))
	   
	   (let-proc-exp (proc-name proc-args proc-body let-body)
		    (let ((proc (proc-val (procedure proc-args proc-body env)))) ;;get the 
		      (value-of let-body
				(extend-env proc-name proc env))))
	   (call-exp (rator rand)
		     (let ((proc (expval->proc (value-of rator env)))
			   (arg (value-of rand env)))
		       (begin
			 ;(print "---------------------enter--call-exp--")
			 ;(print proc)
			 ;(print arg)
			 ;(print "--------------------out--call-exp-----")
			 (apply-procedure proc arg))))
	   )))


(define (extract-free-variables exp)
  (cases expression exp
	 (const-exp (num) '())
	 (var-exp (var) (list var))
	 (diff-exp (exp1 exp2) (append (extract-free-variables exp1)
				       (extract-free-variables exp2)))
	 (zero?-exp (exp1) (extract-free-variables exp1))
	 (if-exp (exp1 exp2 exp3) (append (extract-free-variables exp1)
					  (append (extract-free-variables exp2)
						  (extract-free-variables exp3))))
	 (let-exp (var exp1 body)
		  (delete-var (append (extract-free-variables exp1)
				      (extract-free-variables body))
			      var)) ;; We shouldn't include var in the env
	 (proc-exp (var body)
		   (delete-var (extract-free-variables body)
			       var))
	 (call-exp (var body) (append (extract-free-variables var)
				      (extract-free-variables body)))
	 
	 (else '())
	 ))

;; gen-new-env List * env -> env
(define (gen-new-env vlist env)
  (if (null? vlist) (empty-env)
      (extend-env (car vlist)
		  (apply-env env (car vlist))
		  (gen-new-env (cdr vlist) env))))

(define (remove-dup vlist)
  (makeset (extract-free-variables vlist)))

(define (makeset lat)
  (cond
   [(null? lat) '()]
   [(member? (car lat) (cdr lat))
    (makeset (cdr lat))]
   [else (cons (car lat)
	       (makeset (cdr lat)))]))

(define (member? a lat)
  (cond
   [(null? lat) #f]
   [else (or (eq? (car lat) a)
	     (member? a (cdr lat)))]))

;; delete-var List -> List
;; Delete the element that equals to var in the list.
(define (delete-var vlist var)
  (cond
   [(null? vlist) '()]
   [(eqv? (car vlist) var) (delete-var (cdr vlist) var)]
   [else (cons (car vlist) (delete-var (cdr vlist) var))]))

;; run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;; test code
(run "let f = proc (x) -(x, 1) in (f 1)")
(run "let f = proc (x) proc (y) -(x, y) in ((f 1) 2)")
