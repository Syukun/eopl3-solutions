#lang eopl

proc (x) -(x, 3)
;; ==> (int -> int)

proc (f) proc (x) -((f x), 1)
;; f为一个过程，假设输入为t类型，则 proc (f) 的输入类型为 (t -> int)
;; 输出类型为一个函数 proc (x) 很明显，该函数的输入类型为 t，输出类型为 int
;; 因此这个式子的类型为 ((t -> int) -> (t -> int))

proc (x) x
;; ==> (t -> t)

proc (x) proc (y) (x y)
;; proc (x)的输入为一个函数 假设该函数接收的参数类型为t1，而调用的结果类型为t2
;; 则 ((t1 -> t2) -> (t1 -> t2))

proc (x) (x 3)
;; ==> ((int -> t) -> t)

proc (x) (x x)
;; ((t1 -> t2) -> t2)

proc (x) if x then 88 else 99
;; (bool -> int)

proc (x) proc (y) if x then y else 99
;; (bool -> (int -> int))

(proc (p) if p then 88 else 99
      33)
;; 这个式子有问题，p应该是bool类型，而33是int类型

(proc (p) if p then 88 else 99
      proc (z) z)
;; have no type

proc (f) proc (g) proc (p) proc (x) if (p (f x)) then (g 1) else -((f x), 1)
; 这个玩意个类型比较复杂
; 这里假设x为类型t1 ,我们有 函数f的类型为 (t1 -> int)
; 函数g的类型为 (int -> int)
; 函数p的类型为 (int -> bool)
; 函数x的类型为 (t1 -> int)
; 整个式子的类型为 ((t1 -> int) -> ((int -> int) -> ((int -> bool) -> ((t1 -> int) -> int))))

proc (x) proc (p) proc (f) if (p x) then -(x, 1) else (f p)
; 这里只是式子麻烦一些，其实很简单
; x为int
; p为(int -> bool)
; f为(int -> bool) -> int
; 所以有 (int -> ((int -> bool) -> ((int -> bool) -> int)))

proc (f)
   let d = proc (x)
             proc (z)
               ((f (x x)) z)
   in
      proc (n)
        ((f (d d)) n)
;; 好吧，这个式子也算比较复杂
;假设x为t1类型，则由(x x)有x的输入为 t1,假设输出为t2类型
;则 (t1 -> t2) f的类型为 (t2 -> (t4 -> t5)) 也就是说d的类型为 ((t1 -> t2) -> (t4 -> t5))
;; 算了，我不推导了，总之比较麻烦
;; 
