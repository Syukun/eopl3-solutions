#lang eopl
;;;;;;;;;;;;;;;;;;;; original varsion ;;;;;;;;;;;;;;;;;;;;;;;
(define subst
  (lambda (new old slist)
    (if (null? slist)
        '()
        (cons
         (subst-in-s-exp new old (car slist))
         (subst new old (cdr slist))))))

(define subst-in-s-exp
  (lambda (new old sexp)
    (if (symbol? sexp)
        (if (eqv? sexp old) new sexp)
        (subst new old sexp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; procedure representation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define subst
  (lambda (new old slist)
    (subst/k new old slist (end-cont))))

(define subst/k
  (lambda (new old slist cont)
    (if (null? slist)
        (apply-cont cont '())
        (subst/k new old (cdr slist) (subst-cont new old (car slist) cont)))))

(define subst-cont
  (lambda (new old cur saved-cont)
    (lambda (v)
      (if (symbol? cur)
          (if (eq? cur old)
              (apply-cont saved-cont (cons new v))
              (apply-cont saved-cont (cons cur v)))
          (subst/k new old cur (subst2-cont v saved-cont))))))

(define subst2-cont
  (lambda (cur saved-cont)
    (lambda (val)
      (apply-cont saved-cont (cons val cur)))))

(define apply-cont
  (lambda (cont val)
    (cont val)))

(define end-cont
  (lambda()
    (lambda (v)
      (begin
        (eopl:printf "End of computation.\n")
        (eopl:printf "This sentence should appear only once.\n")
        v))))