#lang eopl
;; 要求我们做cps变换
(lambda (x y) (p (+ 8 x) (q y)))
=
(lambda (x y cont)
  (q y (lambda (v1)
         (p (+ 8 x) v1 cont))))

(lambda (x y u v) (+ 1 (f (g x y) (+ u v))))
=
(lambda (x y u v cont)
  (g x y lambda (v1)
     (f v1 (+ u v) lambda (v2)
        (+ 1 v2 cont))))

(+ 1 (f (g x y) (+ u (h v))))
=
(g x y lambda (v1)
   (h v lambda (v2)
      (+ u v2 lambda (v3)
         (f v1 v3 lambda (v4)
            (+ 1 v4 cont)))))

(zero? (if a (p x) (p y)))
=
(a lambda (val)
   (if val
       (p x lambda (v1) (zero? v1))
       (p y lambda (v2) (zero? v2))))

(zero? (if (f a) (p x) (q y)))
=
(f a (lambda (val)
       (if val
           (p x (lambda (v1) (zero? v1)))
           (q y (lambda (v2) (zero? v2))))))

(let ((x (let ((y 8)) (p y)))) x)
=
(y 8 (lambda (var)
       (p y (lambda (val)
              (let ((var val))
                var (lambda (val)
                      (let ((x val))
                        x)))))))

(let ((x (if a (p x) (p y)))) x)
=
(a (lambda (val)
     (if val
         (p x (lambda (v1)
                (let ((x v1)) x)))
         (p y (lambda (v2)
                (let ((x v2)) x))))))
            
   
