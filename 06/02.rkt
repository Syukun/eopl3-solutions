#lang eopl
;用归纳法证明，(fib/k n g) = (g (fib n))
(define fib
  (lambda (n)
    (fib/k n (lambda (val) val))))

(define fib/k
  (lambda (n cont)
    (if (< n 2)
        (cont 1)
        (fib/k (- n 1)
               (lambda (val1)
                 (fib/k (- n 2)
                        (lambda (val2)
                          (cont (+ val1 val2)))))))))

;; 好吧，我试图来证明一下
;; (fib/k 1 g) = (g 1) = 1
;; 我们假设 (fib/k n g) = (g (fib n)),我们要证明 (fib/k (n+1) g) = (g (fib (n+1))
(fib/k (n+1) g) =
(fib/k n
       (lambda (val1)
         (fib/k (- n 1)
                (lambda (val2)
                  (g (+ val1 val2)))))) ;; 接下来要如何证明呢？
=
((lambda (val1)
   (fib/k (- n 1)
          (lambda (val2)
            (g (+ val1 val2)))))
 (fib n))
=
(fib/k (- n 1)
       (lambda (val2)
         (g (+ (fib n) val2)))) ;; 然后继续
= ((lambda (val2)
    (g (+ (fib n) val2)))
   (fib (- n 1)))
= (g (+ (fib n) (fib (- n 1))))
= (g (fib (+ n 1)))
;好吧！证明完毕！

