#lang eopl
;; 事实上，书上的代码存在一点问题。这里修改一下。

(define-datatype continuation continuation?
  (end-cont)
  (fact1-cont
   (saved-n number?)
   (saved-cont continuation?))
  )

(define n 'uninitialized)
(define cont 'uninitialized)
(define val 'uninitialized)
(define pc 'uninitialized)

(define fact
  (lambda (arg-n)
    (set! cont (end-cont))
    (set! n arg-n)
    (set! pc fact/k)
    (trampoline!)
    val))

(define trampoline!
  (lambda ()
    (if pc
        (begin
          (pc)
          (trampoline!))
        #f)))

(define fact/k
  (lambda ()
    (if (zero? n)
        (begin
          (set! val 1)
          (set! pc apply-cont))
        (begin
          (set! cont (fact1-cont n cont))
          (set! n (- n 1))
          ;(set! pc fact/k)
          ))))

(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont ()
                (set! pc #f))
      (fact1-cont (saved-n saved-cont)
                  (set! cont saved-cont)
                  (set! val (* val saved-n))
                  (set! n saved-n)
                  ;(set! pc apply-cont)
                  ))))
 ;; 好吧，去除了fact/k中的(set! pc fact/k)以及apply-cont中的(set! pc apply-cont)代码依然运行正常.
;; 其实非常简单，因为在fact/k中调用(set! pc fact/k)的时候，pc的值已经是fact/k
;; 同理对apply-cont也适用
