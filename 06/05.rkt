#lang eopl

;; 算了，要我一个一个去改那些玩意太麻烦了，直接用我参考的例子吧！

(let [x (if a (p x) (p y))] x)
=
(if a (p x) (p y))
=
(lambda (x y cont)
  (p x lambda (v1)
     (cont (if a v1 (p y cont)))))
=
(lambda (a x y cont)
  (p y (lambda (v2)
         (p x (lambda (v1)
                (cont (if a v1 v2)))))))
