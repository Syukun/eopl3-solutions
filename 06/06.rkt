#lang eopl
;; how many different evaluation orders are possible for the procedure calls in
;; (lambda (x y) (+ (f (g x)) (h (j y))))

(lambda (x y cont)
   (j y lambda (v1)
     (g x lambda (v2)
        (f v2 lambda (v3)
           (h v1 lambda (v4)
              (cont (+ v3 v4)))))))

(lambda (x y cont)
  (j y lambda (v1)
     (g x lambda (v2)
        (h v1 lambda (v3)
           (f v2 lambda (v4)
              (cont (+ v3 v4)))))))

(lambda (x y cont)
  (g x (lambda (v1)
         (j y lambda (v2)
            (h v2 lambda (v3)
               (f v1 lambda (v4)
                  (cont (+ v3 v4))))))))

(lambda (x y cont)
  (g x (lambda (v1)
         (j y lambda (v2)
            (f v1 lambda (v3)
               (h v2 lambda (v4)
                  (cont (+ v3 v4))))))))

(lambda (x y cont)
  (g x (lambda (v1)
         (f v1 lambda (v2)
            (j y lambda (v3)
               (h v3 lambda (v4)
                  (cont (+ v2 v4))))))))

(lambda (x y cont)
  (j y lambda (v1)
     (h v1 (lambda (v2)
             (g x lambda (v3)
                (f v3 lambda (v4)
                   (cont (+ v2 v4))))))))
...

