#lang eopl
;;;;;;;;;;;;;;;;;;;; original version ;;;;;;;;;;;;;;;;;;;;;;

(define occurs-free?
  (lambda (var exp)
    (cond
      [(symbol? exp) (eqv? var exp)]
      [(eqv? (car exp) 'lambda)
       (and
        (not (eqv? var (car (cadr exp))))
        (occurs-free? var (caddr exp)))]
      [else
       (or
        (occurs-free? var (car exp))
        (occurs-free? var (cadr exp)))])))

;;;;;;;;;;;;;;;;;;;;;;;;;; procedure representation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define end-cont
   (lambda ()
     (lambda (val)
      (begin
        (eopl:printf "End of computation.\n")
        (eopl:printf "This sentence should appear only once.\n")
        val))))

(define apply-cont
  (lambda (cont val)
    (cont val)))

(define occurs-free?
  (lambda (var exp)
    (occurs-free?/k var exp (end-cont))))


(define occurs-free?/k
  (lambda (var exp cont)
    (cond
      [(symbol? exp) (apply-cont cont (eqv? var exp))]
      [(eqv? (car exp) 'lambda)
       (my-not (eqv? var (car (cadr exp))) (occurs-free-cont var (caddr exp) cont))]
      [else
       (occurs-free?/k var (car exp) (occurs-free-or-cont var (cadr exp) cont))
       ])))

(define occurs-free-or-cont
  (lambda (var exp saved-cont)
    (lambda (v)
      (if v
          (apply-cont saved-cont #t)
          (occurs-free?/k var exp (my2-cont saved-cont))))))

(define my2-cont
  (lambda (saved-cont)
    (lambda (v)
      (apply-cont saved-cont v))))

(define my-not
  (lambda (exp cont)
    (apply-cont cont (not exp))))

(define occurs-free-cont
  (lambda (var exp saved-cont)
    (lambda (v)
      (if v
          (occurs-free?/k var exp (my-cont saved-cont))
          (apply-cont saved-cont #f)))))

(define my-cont
  (lambda (saved-cont)
    (lambda (v)
      (apply-cont saved-cont v))))


