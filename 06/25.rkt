#lang eopl
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
     ("+" "(" (separated-list expression ",") ")")
     sum-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression
     ("letrec"
      (arbno identifier "(" (arbno identifier) ")"
             "=" expression)
      "in"
      expression)
     letrec-exp)
    
    (expression (identifier) var-exp)
    
    ;; New stuff
    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)
    
    (expression
     ("proc" "(" (arbno identifier) ")" expression)
     proc-exp)
    
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    ))


  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;
(define cps-out-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define cps-out-grammar
  '((cps-out-program (tfexp) cps-a-program)

    (simple-expression (number) cps-const-exp)

    (simple-expression (identifier) cps-var-exp)

    (simple-expression
     ("-" "(" simple-expression "," simple-expression ")")
     cps-diff-exp)

    (simple-expression
     ("zero?" "(" simple-expression ")")
     cps-zero?-exp)

    (simple-expression
     ("+" "(" (separated-list simple-expression ",") ")")
     cps-sum-exp)

    (simple-expression
     ("proc" "(" (arbno identifier) ")" tfexp)
     cps-proc-exp)

    (tfexp
     (simple-expression)
     simple-exp->exp)

    ;; 这里稍微改变了一下，使得let可以带多个变量
    (tfexp
     ("let" (arbno identifier "=" simple-expression) "in" tfexp)
     cps-let-exp)

    (tfexp
     ("letrec"
      (arbno identifier "(" (arbno identifier) ")"
             "=" tfexp)
      "in"
      tfexp)
     cps-letrec-exp)

    (tfexp
     ("if" simple-expression "then" tfexp "else" tfexp)
     cps-if-exp)

    (tfexp
     ("(" simple-expression (arbno simple-expression) ")")
     cps-call-exp)

    ))

;;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes cps-out-lexical-spec cps-out-grammar)

(define cps-show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes cps-out-lexical-spec cps-out-grammar)))

(define cps-out-scan&parse
  (sllgen:make-string-parser cps-out-lexical-spec cps-out-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; cps ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define debug #t)
;; cps-of-program : InpExp -> TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (if debug (eopl:printf "cps-of-program :\n exp1 -> ~a\n" exp1) #f)
                 (cps-a-program
                  (cps-of-exps (list exp1)
                               (lambda (new-args) 
                                 (simple-exp->exp (car new-args)))))))))

;; cps-of-exp : Exp * SimpleExp -> TfExp
(define cps-of-exp
  (lambda (exp cont)
    (cases expression exp
      (const-exp (num) (make-send-to-cont cont (cps-const-exp num)))
      (var-exp (var) (make-send-to-cont cont (cps-var-exp var)))
      (proc-exp (vars body) 
                (make-send-to-cont cont
                                   (cps-proc-exp (append vars (list 'k%00))
                                                 (cps-of-exp body (cps-var-exp 'k%00)))))
      (zero?-exp (exp1)
                 (cps-of-zero?-exp exp1 cont))
      (diff-exp (exp1 exp2)
                (cps-of-diff-exp exp1 exp2 cont))
      (sum-exp (exps)
               (cps-of-sum-exp exps cont))
      (if-exp (exp1 exp2 exp3)
              (cps-of-if-exp exp1 exp2 exp3 cont))
      (let-exp (vars exps body)
               (eopl:printf "cps-of-exp * let-exp :\n var -> ~a\n exp1 -> ~a\n body -> ~a\n" vars exps body) 
               (cps-of-let-exp vars exps body cont))
      (letrec-exp (ids bidss proc-bodies body)
                  (cps-of-letrec-exp ids bidss proc-bodies body cont))
      (call-exp (rator rands)
                (eopl:printf "cps-of-exp * call-exp :\n rator -> ~a\n rands -> ~a\n" rator rands)
                (cps-of-call-exp rator rands cont)))))

;; cps-of-exps : Listof(InpExp) * (Listof(InpExp) -> TfExp) 
;;                -> TfExp
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ((exps exps))
      ;; cps-of-rest : Listof(InpExp) -> TfExp
      (let ((pos (list-index
                  (lambda (exp)
                    (not (inp-exp-simple? exp)))
                  exps)))
        (if (not pos)
            (begin
              ;(eopl:printf "cps-of-exps3 :\n exps -> ~a\n" exps)
              (builder (map cps-of-simple-exp exps)))
            (let ((var (fresh-identifier 'var)))
              (begin
                ;(eopl:printf "cps-of-exps :\n var -> ~a\n" var)
                ;(eopl:printf "cps-of-exps1 :\n exps -> ~a\n" exps)
                (cps-of-exp
                 (begin
                   ;(eopl:printf "cps-of-exps :\n ref -> ~a\n" (list-ref exps pos))
                   (list-ref exps pos))
                 (cps-proc-exp (list var)
                               (cps-of-rest
                                (begin 
                                  ;(eopl:printf "cps-of-exps2 :\n exps -> ~a\n" (list-set exps pos (var-exp var)))
                                  (list-set exps pos (var-exp var))
                                  )))))))))))

;; inp-exp-simple? : InpExp -> Bool
;; returns #t or #f, depending on whether exp would be a 
;; simple-exp if reparsed using the CPS-OUT language.
(define inp-exp-simple?
  (lambda (exp)
    (cases expression exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2)
                (and
                 (inp-exp-simple? exp1)
                 (inp-exp-simple? exp2)))
      (zero?-exp (exp1)
                 (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps)
               (all-simple? exps))
      (else #f))))

(define all-simple?
  (lambda (exps)
    (if (null? exps)
        #t
        (and (inp-exp-simple? (car exps))
             (all-simple? (cdr exps))))))


;; takes a list of expressions and finds the position of the first
;; one that is not a simple-exp, else returns #f
(define index-of-first-non-simple
  (lambda (exps)
    (cond
      ((null? exps) #f)
      ((inp-exp-simple? (car exps))
       (let ((pos (index-of-first-non-simple (cdr exps))))
         (if pos
             (+ pos 1) #f)))
      (else 0))))

;; cps-of-simple-exp : InpExp -> SimpleExp
;; Page: 220
;; assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp)
    (cases expression exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp
                 (cps-of-simple-exp exp1)
                 (cps-of-simple-exp exp2)))
      (zero?-exp (exp1)
                 (cps-zero?-exp
                  (cps-of-simple-exp exp1)))
      (proc-exp (ids exp) 
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp exp (cps-var-exp 'k%00))))
      (sum-exp (exps)
               (cps-sum-exp
                (map cps-of-simple-exp exps)))
      (else 
       (report-invalid-exp-to-cps-of-simple-exp exp)))))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-simple-of-exp
                "non-simple expression to cps-of-simple-exp: ~s"
                exp)))

;; make-send-to-cont : SimpleExp * SimpleExp -> TfExp
(define make-send-to-cont
  (lambda (cont bexp)
    (cps-call-exp cont (list bexp))))

;; cps-of-zero?-exp : InpExp * SimpleExp -> TfExp
(define cps-of-zero?-exp
  (lambda (exp1 k-exp) 
    (cps-of-exps (list exp1)
                 (lambda (new-rands)
                   (make-send-to-cont
                    k-exp
                    (cps-zero?-exp 
                     (car new-rands)))))))

;; cps-of-sum-exp : Listof (InpExp) * SimpleExp -> TfExp
(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (new-rands)
                   (make-send-to-cont
                    k-exp
                    (cps-sum-exp new-rands))))))

;; cps-of-diff-exp : InpExp * InpExp * SimpleExp -> TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps
     (list exp1 exp2)
     (lambda (new-rands)
       (make-send-to-cont
        k-exp
        (cps-diff-exp
         (car new-rands)
         (cadr new-rands)))))))

;; cps-of-if-exp : InpExp * InpExp * InpExp * SimpleExp -> TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (eopl:printf "cps-of-if-exp :\n k-exp -> ~a\n" k-exp)
    (cps-of-exps (list exp1)
                 (lambda (new-rands)
                   (cps-if-exp (car new-rands)
                               (cps-of-exp exp2 k-exp) ;; k-exp 代表cps-of-exp中的cont参数
                               (cps-of-exp exp3 k-exp))))))

;; cps-of-let-exp : Var * InpExp * InpExp * SimpleExp -> TfExp
(define cps-of-let-exp
  (lambda (id rhs body k-exp) 
    (eopl:printf "cps-of-let-exp :\n id -> ~a\n rhs -> ~a\n body -> ~a\n k-exp -> ~a\n" id rhs body k-exp)
    (cps-of-exps (list rhs)
                 (lambda (new-rands)
                   (cps-let-exp id 
                                (car new-rands)
                                (cps-of-exp body k-exp))))))

;; cps-of-letrec-exp :
;; Listof(Listof(Var)) * Listof(InpExp) * InpExp * SimpleExp -> TfExp
(define cps-of-letrec-exp
  (lambda (proc-names idss proc-bodies body k-exp)
    (cps-letrec-exp
     proc-names
     (map
      (lambda (ids) (append ids (list 'k%00)))
      idss)
     (map
      (lambda (exp) (cps-of-exp exp (cps-var-exp 'k%00)))
      proc-bodies)
     (cps-of-exp body k-exp))))

;; cps-of-call-exp : InpExp * Listof(InpExp) * SimpleExp -> TfExp
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (eopl:printf "cps-of-call-exp :\n rator -> ~a\n rands -> ~a\n k-exp -> ~a\n" rator rands k-exp)
    (eopl:printf "cps-of-call-exp :\n cons rator rands -> ~a \n" (cons rator rands))
    (cps-of-exps (cons rator rands)
                 (lambda (new-rands)
                   (cps-call-exp
                    (car new-rands)
                    (append (cdr new-rands) (list k-exp)))))))

;;;;;;;;;;;;;;;; utilities ;;;;;;;;;;;;;;;;

(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)  
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

;; list-set : SchemeList * Int * SchemeVal -> SchemeList
;; returns a list lst1 that is just like lst, except that 
;; (listref lst1 n) = val.
(define list-set
  (lambda (lst n val)
    (cond
      ((null? lst) (eopl:error 'list-set "ran off end"))
      ((zero? n) (cons val (cdr lst)))
      (else (cons (car lst) (list-set (cdr lst) (- n 1) val))))))

;; list-index : (SchemeVal -> Bool) * SchemeList -> Maybe(Int)
;; returns the smallest number n such that (pred (listref lst n))
;; is true.  If pred is false on every element of lst, then returns
;; #f. 
(define list-index
  (lambda (pred lst)
    (cond
      ((null? lst) #f)
      ((pred (car lst)) 0)
      ((list-index pred (cdr lst)) => (lambda (n) (+ n 1)))
      (else #f))))




