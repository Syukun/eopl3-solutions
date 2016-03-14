(load-relative "../libs/init.scm")
(load-relative "./base/environments.scm")
(load-relative "./base/proc-lang.scm")
;; I think this is a little difficult, see the new stuff

;; I come across some serious problem that I can't write a grammer as follows:
;; letrec f (x) = 1 y(x) = 2 in 1
;; (expression ("letrec" (arbno identifier "(" identifier ")" "=" expression) in expression) letrec-exp)
;; It didn't work, and compiler tells me that it isn't LL.
;; Ok, so Maybe I will complete it another day!

;; new stuff
(run "let even-iter = proc (o) proc(e) proc(num)
      if zero?(num)
          then 1
      else
          (((o o) e) -(num, 1))
      in let odd-iter = proc (o) proc(e) proc(num)
      if zero?(num)
           then 0
      else
          (((e o) e) -(num, 1))
      in let odd = proc(num) (((odd-iter odd-iter) even-iter) num)
        in let even = proc(num) (((even-iter odd-iter) even-iter) num)
            in (odd 6)")

