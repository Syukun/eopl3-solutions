#lang eopl
;; 写一个inlined representations表示

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (lambda (val) val))))))

(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (cont (num-val num)))
      (var-exp (var) (cont (apply-env env var)))
      (proc-exp (var body)
                (cont (proc-val (procedure var body env))))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of/k letrec-body (extend-env-rec p-name b-var p-body env)
                              cont))
      (zero?-exp (exp1) (value-of/k exp1 env
                                    (lambda (val)
                                      (cont (bool-val (zero? (expval->num val)))))))
      (let-exp (var exp1 body)
               (vlaue-of/k exp1 env
                           (lambda (val) (value-of/k body (extend-env var val env) cont))))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (lambda (val) (if (expval->bool val)
                                            (value-of/k exp2 env cont)
                                            (value-of/k exp3 env cont)))))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (lambda (val1)
                              (value-of/k exp2 env
                                          (lambda (val2)
                                            (cont (num-val (- val1 val2))))))))
      (call-exp (rator rand)
                (value-of/k rator env
                            (lambda (rator)
                              (value-of/k rand env
                                          (lambda (rand)
                                            (let ((proc (expval->proc rator)))
                                              (apply-procedure/k proc rand cont)))))))
      
      )))

(define apply-procedure/k
  (lambda (proc1 arg cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var arg saved-env)
                             cont))))) 