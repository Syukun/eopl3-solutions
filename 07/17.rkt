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
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    (expression (identifier) var-exp)

    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("proc" "("  identifier ":" optional-type ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("letrec"
      optional-type identifier "(" identifier ":" optional-type ")"
      "=" expression "in" expression)
     letrec-exp)

    (optional-type
     ("?")
     no-type) ;; 可选的参数

    (optional-type
     (type)
     a-type) ;; a-type是什么玩意

    (type
     ("int")
     int-type)

    (type
     ("bool")
     bool-type)

    (type
     ("(" type "->" type ")")
     proc-type)

    (type
     ("%tvar-type" number)
     tvar-type)

    ))
 ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;; apply-one-subst : Type * Tvar * Type -> Type
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (apply-one-subst arg-type tvar ty1)
                  (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))

;; apply-subst-to-type : Type * Subst -> Type
;; 好吧，这个式子也是非常漂亮的一个式子
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type t1 subst)
                  (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
                 (let ([tmp (assoc ty subst)])
                   (if tmp
                       (cdr tmp)
                       ty))))))

;; empty-subst : () -> Subst
(define empty-subst (lambda () '()))

;; extend-subst : Subst * Tvar * Type -> Subst
(define extend-subst
  (lambda (subst tvar ty)
    (cons
     (cons tvar ty)
     (map
      (lambda (p)
        (let ([oldlhs (car p)]
              [oldrhs (cdr p)])
          (cons
           oldlhs
           (apply-one-subst oldrhs tvar ty)))) ;; 将右边的东西中的tvar替换为ty
      subst))))

;; new stuff
(define extend-subst-m
  (lambda (subst tvar ty)
    (cons (cons tvar ty) subst))) ;; 这么做的话会导致没有替换是吧。

;; 其余的工作移步到了apply-subst-to-type里面,也就是说在apply-sub-to-type里面，要将tvar替换为ty
(define apply-subst-to-type-m
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type
                  (apply-subst-to-type-m t1 subst)
                  (apply-subst-to-type-m t2 subst)))
     (tvar-type (sn)
                 (let ([tmp (assoc ty subst)])
                   (if tmp
                       (apply-subst-to-type-m (cdr tmp) subst) ;; 重新另外寻找
                       ty))))))

(extend-subst (empty-subst) 'var (int-type))
(extend-subst
 (extend-subst
  (extend-subst (empty-subst) 'var (bool-type))
  'xx (int-type))
 'vv (bool-type))

;; test code
(define m (extend-subst-m (extend-subst-m (empty-subst) (tvar-type 1) (tvar-type 2)) (tvar-type 2) (int-type)))

(apply-subst-to-type-m (tvar-type 1) m)

