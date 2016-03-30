#lang eopl
(require "./base/cps.rkt")
(require "./base/cps-out-lang.rkt")
(require "./base/data-structures.rkt")

;; 题目要求我们完全移除cont
(define value-of-simple-exp
  (lambda (exp env)
    (cases simple-expression exp
      (cps-const-exp (num) (num-val num))
      (cps-var-exp (var) (apply-env env var))
      (cps-diff-exp (exp1 exp2)
                    ;(eopl:printf "cps-diff-exp :\n exp1 -> ~a\n exp2 -> ~a\n" exp1 exp2)
                    (let [(v1 (expval->num (value-of-simple-exp exp1 env)))
                          (v2 (expval->num (value-of-simple-exp exp2 env)))]
                      (num-val (- v1 v2))))
      (cps-zero?-exp (exp1)
                     (bool-val (zero? (expval->num (value-of-simple-exp exp1 env)))))
      (cps-sum-exp (exps)
                   (let [(nums (map (lambda (exp)
                                      (expval->num (value-of-simple-exp exp env)))
                                    exps))]
                     (num-val (foldl + 0 nums))))
      (cps-proc-exp (vars body)
                    (proc-val
                     (procedure vars body env)))
      )))

(define foldl
  (lambda (f acc li)
    (if (null? li) acc
        (foldl +
               (f (car li) acc)
               (cdr li)))))

;; value-of/k : TfExp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env)
    (cases tfexp exp
      (simple-exp->exp (simple) (value-of-simple-exp simple env))
      
      (cps-let-exp (var rhs body)
               (let [(val (value-of-simple-exp rhs env))]
                 (value-of/k body
                             (extend-env-rec** (list var) (list val) env))))
      
      (cps-if-exp (simple1 body1 body2)
              (if (expval->bool (value-of-simple-exp simple1 env))
                  (value-of/k body1 env)
                  (value-of/k body2 env)))

      (cps-call-exp (rator rands)
                (let [(rator-proc
                       (expval->proc
                        (value-of-simple-exp rator env)))
                      (rand-vals
                       (map
                        (lambda (simple)
                          (value-of-simple-exp simple env))
                        rands))]
                  (apply-procedure/k rator-proc rand-vals)))
      (else #f)
      )))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define apply-procedure/k
  (lambda (proc1 args)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of/k body
                             (extend-env* vars args saved-env))))))

(define value-of-program
  (lambda (pgm)
    ;(eopl:printf "pgm -> ~a\n" pgm)
    (cases cps-out-program pgm
           (cps-a-program (exp1)
                          ;(eopl:printf "exp1 -> ~a\n" exp1)
                          (value-of/k exp1 (init-env))))))
(define run
  (lambda (string)
    (let ((cpsed-pgm
	   (cps-of-program (scan&parse string))))
      (value-of-program cpsed-pgm))))
                     


