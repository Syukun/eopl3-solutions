#lang eopl
(require "./base/cps.rkt")
(require "./base/cps-out-lang.rkt")
(require "./base/data-structures.rkt")
;; trampoline the interpreter.
;; 下面的实现还是不太完整，因为完整的trampoline应该是像cpu一样，将下一步要运行的代码放入pc中，我这个暂时还不行。

(define r-cont 'uninitialized)
(define r-val 'uninitialized)
(define r-exp 'uninitialized)
(define r-env 'uninitialized)
(define r-rator 'uninitialized)
(define r-rands 'uninitialized)
(define r-pc 'uninitialized)

(define trampoline!
  (lambda ()
    (if r-pc
        (begin
          (r-pc)
          (trampoline!))
        #f)))

(define value-of-simple-exp
  (lambda ()
    (cases simple-expression r-exp
      
      (cps-const-exp (num)
                     (set! r-val (num-val num)))
      
      (cps-var-exp (var)
                   (set! r-val (apply-env r-env var)))
      
      (cps-diff-exp (exp1 exp2)
                    (set! r-exp exp1)
                    (value-of-simple-exp)
                    (let [(v1 (expval->num r-val))]
                      (begin
                        (set! r-exp exp2)
                        (value-of-simple-exp)
                        (let [(v2 (expval->num r-val))]
                          (begin
                            (set! r-val (num-val (- v1 v2)))
                            )))))
      
      (cps-zero?-exp (exp1)
                     (set! r-exp exp1)
                     (set! r-pc value-of-simple-exp)
                     (set! r-val (bool-val (zero? (expval->num r-val)))))
      
      (cps-sum-exp (exps)
                   (let [(nums (map (lambda (exp)
                                      (set! r-exp exp)
                                      (set! r-pc value-of-simple-exp)
                                      (expval->num r-val))
                                    exps))]
                     (set! r-val (num-val (foldl + 0 nums)))))
      
      (cps-proc-exp (vars body)
                     (set! r-val (proc-val (procedure vars body r-env))))
      )))

(define foldl
  (lambda (f acc li)
    (if (null? li) acc
        (foldl +
               (f (car li) acc)
               (cdr li)))))

;; value-of/k : TfExp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda ()
    (cases tfexp r-exp
      (simple-exp->exp (simple)
                       (set! r-exp simple)
                       (value-of-simple-exp)
                       (set! r-pc apply-cont))
      
      (cps-let-exp (var rhs body)
                   (set! r-exp rhs)
                   (value-of-simple-exp)
                   (set! r-env (extend-env* (list var) (list r-val) r-env))
                   (set! r-exp body)
                   (set! r-pc value-of/k))
              
      (cps-if-exp (simple1 body1 body2)
                  (set! r-exp simple1)
                  (value-of-simple-exp)
                  (let [(val (expval->bool r-val))]
                    (if val
                        (begin
                          (set! r-exp body1)
                          (set! r-pc value-of/k))
                        (begin
                          (set! r-exp body2)
                          (set! r-pc value-of/k)))))

      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (set! r-exp letrec-body)
                      (set! r-env (extend-env-rec** p-names b-varss p-bodies r-env))
                      (set! r-pc value-of/k))
      
      (cps-call-exp (rator rands)
                    (set! r-exp rator)
                    (value-of-simple-exp)
                    (let [(rator-proc (expval->proc r-val))
                          (rand-vals (map
                                      (lambda (simple)
                                        (set! r-exp simple)
                                        (value-of-simple-exp)
                                        r-val) rands))]
                      (set! r-rator rator-proc)
                      (set! r-rands rand-vals)
                      (set! r-pc apply-procedure/k)))
      (else
       (begin
         (set! r-val #f)
         (set! r-pc apply-cont))) 
      )))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure/k
  (lambda ()
    (cases proc r-rator
      (procedure (vars body saved-env)
                 (set! r-exp body)
                 (set! r-env (extend-env* vars r-rands saved-env))
                 (set! r-pc value-of/k)))))

;; apply-cont : Cont * ExpVal -> Final-ExpVal
(define apply-cont
  (lambda ()
    (cases continuation r-cont
        (end-cont ()
                  (begin
                     (set! r-pc #f)
                     r-val)))))

(define value-of-program
  (lambda (pgm)
    ;(eopl:printf "pgm -> ~a\n" pgm)
    (cases cps-out-program pgm
           (cps-a-program (exp1)
                          (set! r-exp exp1)
                          (set! r-env (init-env))
                          (set! r-cont (end-cont))
                          (set! r-pc value-of/k)
                          (trampoline!)
                          r-val))))
(define run
  (lambda (string)
    (let ((cpsed-pgm
	   (cps-of-program (scan&parse string))))
      (value-of-program cpsed-pgm))))

;; test code
;; 这个玩意并没有完整实现,比如说下面的letrec表达式就没有实现


