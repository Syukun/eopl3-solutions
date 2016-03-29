#lang eopl
;; 原来的版本是这样的：
(define list-sum
  (lambda (loi)
    (if (null? loi)
        0
        (+ (car loi)
           (list-sum (cdr loi))))))

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

(define list-sum
  (lambda (loi)
    (list-sum/k loi (end-cont))))

(define list-sum/k
  (lambda (loi cont)
    (if (null? loi)
        (apply-cont cont 0)
        (list-sum/k (cdr loi) (list-sum-cont (car loi) cont)))))

(define list-sum-cont
  (lambda (saved-n saved-cont)
    (lambda (val)
      (apply-cont saved-cont (+ saved-n val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;; data structure representation ;;;;;;;;;;;;;;;;;;;;;;;
(define list-sum
  (lambda (loi)
    (list-sum/k loi (end-cont))))

(define list-sum/k
  (lambda (loi cont)
    (if (null? loi)
        (apply-cont cont 0)
        (list-sum/k (cdr loi) (list-sum-cont (car loi) cont)))))

(define-datatype continuation continuation?
  (end-cont)
  (list-sum-cont
   (saved-n number?)
   (svaed-cont continuation?)))

(define apply-cont
  (lambda (cont val)
     (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.\n")
                (eopl:printf "This sentence should appear only once.\n")
                val)
      (list-sum-cont (saved-n saved-cont)
                     (apply-cont saved-cont (+ saved-n val))))))
;;;;;;;;;;;;;;;;;;;;;;;;;; inline ;;;;;;;;;;;;;;;;;;;;;;;
(define list-sum
  (lambda (loi)
    (list-sum/k loi
                (lambda (val)
                      (eopl:printf "End of computation.\n")
                      (eopl:printf "This sentence should appear only once.\n")
                      val))))

(define list-sum/k
  (lambda (loi cont)
    (if (null? loi)
        (cont 0)
        (list-sum/k (cdr loi) (lambda (val) (cont (+ val (car loi))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;; registerized ;;;;;;;;;;;;;;;;;;;;;;;
(define cont 'uninitialized)
(define loi 'uninitialized)
(define val 'uninitialized)
(define pc 'uninitialized)

(define list-sum
  (lambda (a-loi)
    (set! cont (end-cont))
    (set! pc list-sum/k)
    (set! loi a-loi)
    (trampoline)
    val))

(define trampoline
  (lambda ()
    (if pc
        (begin
          (pc)
          (trampoline))
        #f)))

(define list-sum/k
  (lambda ()
    (if (null? loi)
        (begin
          (set! val 0)
          (set! pc apply-cont))
       (begin
         (set! cont (list-sum-cont (car loi) cont))
         (set! loi (cdr loi))
         (set! pc list-sum/k)))))

(define-datatype continuation continuation?
  (end-cont)
  (list-sum-cont
   (saved-n number?)
   (svaed-cont continuation?)))

(define apply-cont
  (lambda ()
     (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.\n")
                (eopl:printf "This sentence should appear only once.\n")
                (set! pc #f))
      (list-sum-cont (saved-n saved-cont)
                     (set! val (+ saved-n val))
                     (set! cont saved-cont)
                     (set! pc apply-cont)))))
                     