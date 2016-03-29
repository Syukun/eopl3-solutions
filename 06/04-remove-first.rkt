#lang eopl
;; 原来版本的remove-first
;(define remove-first
;  (lambda (s los)
;    (if (null? los)
;        '()
;        (if (eqv? (car los) s)
;            (cdr los)
;            (cons (car los) (remove-first s (cdr los)))))))

;; 这玩意怎么玩，怎么不给一个例子呢？
(define remove-first
  (lambda (s los)
    (remove-first/k s los (end-cont))))

(define remove-first/k
  (lambda (s los cont)
    (if (null? los)
        (apply-cont cont '())
        (if (eqv? (car los) s)
            (apply-cont cont (cdr los))
            (remove-first/k s (cdr los) (remove-cont (car los) cont))))))
;; procedure representation
(define remove-cont
  (lambda (n cont)
    (lambda (val)
      (apply-cont cont (append (list n) val)))))

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

;; data structure representation
(define-datatype continuation continuation?
  (end-cont)
  (remove-cont
   (saved-n number?)
   (svaed-cont continuation?)))

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.\n")
                (eopl:printf "This sentence should appear only once.\n")
                val)
      (remove-cont (saved-n saved-cont)
                   (apply-cont saved-cont (append (list saved-n) val))))))

;; inline
(define remove-first
  (lambda (s los)
    (remove-first/k s los
                    (lambda (val)
                      (eopl:printf "End of computation.\n")
                      (eopl:printf "This sentence should appear only once.\n")
                      val))))

(define remove-first/k
  (lambda (s los cont)
    (if (null? los)
        (cont '())
        (if (eqv? (car los) s)
            (cont (cdr los))
            (remove-first/k s (cdr los)
                            (lambda (val) (let [(current (car los))]
                                            (cont (append (list current) val)))))))))

;; registed
#lang eopl
(define pc 'uninitialized)
(define cont 'unintitialized)
(define val 'uninitialized)
(define s 'uninitialized)
(define los 'uninitialized)

(define-datatype continuation continuation?
  (end-cont)
  (remove-cont
   (saved-n number?)
   (svaed-cont continuation?)))

(define remove-first
  (lambda (a-s a-los)
    (set! s a-s) ;; 两个参数 s和 los
    (set! los a-los)
    (set! cont (end-cont))
    (set! pc remove-first/k)
    (trampoline)
    val))

(define trampoline
  (lambda ()
    (if pc
        (begin
          (pc)
          (trampoline))
        #f)))

(define remove-first/k
  (lambda ()
    (if (null? los)
        (begin
          (set! val '())
          (set! pc apply-cont))
        (if (eqv? (car los) s)
            (begin
              (set! val (cdr los))
              (set! pc apply-cont))
            (begin
              ;(eopl:printf "car los -> ~a\n" (car los))
              (set! cont (remove-cont (car los) cont))
              (set! los (cdr los))
              ;; 副作用实在太强,注意书写的顺序
             ; (eopl:printf "cont -> ~a\n" cont)
              (set! pc remove-first/k))))))

(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.\n")
                (eopl:printf "This sentence should appear only once.\n")
                (set! pc #f))
      (remove-cont (saved-n saved-cont)
                    (set! cont saved-cont)
                    (set! val (append (list saved-n) val))
                    (set! pc apply-cont)))))


                      
