#lang eopl
;; 下面的表达式出了什么错误
letrec
 ? even (odd : ?) =
      proc (x : ?)
        if zero?(x) then 1 else (odd -(x, 1))
 in letrec
     ? odd(x : bool) =
        if zero?(x) then 0 else ((even odd) -(x, 1))
     in (odd 13)

;; 我们来推断一下吧，在even函数里，x为int类型，odd是一个函数，接收一个int作为其的参数返回一个int
;; 所以even的类型为((int -> int) -> (int -> int))
;; 到了下面的这个odd这个函数x为bool类型，而zero要求一个int，冲突，出现了错误

