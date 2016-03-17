#lang eopl
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   parse
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    (expression ("(" expression expression ")") call-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    ;; new stuff
    ;(expression ("letrec" (arbno identifier "(" identifier ")" "=" expression) "in" expression) letrec-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    
    (expression ("%nameless-var" number) nameless-var-exp)
    (expression ("%nameless-letrec-var" number) nameless-letrec-var-exp)
    
    (expression ("%let" expression "in" expression) nameless-let-exp)
    (expression ("%letrec" expression "in" expression) nameless-letrec-exp)
    (expression ("%proc" expression) nameless-proc-exp)
    (expression ("%unpack" expression "in" expression) nameless-unpack-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))