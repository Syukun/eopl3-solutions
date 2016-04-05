#lang eopl
;; 如何写一个规则？好吧，随便写一写吧。

letrec ? f (x : ?)
        = if zero?(x) then 0 else -((f -(x, 1)), -2)
in f
;; x : int
;; f : int -> int

letrec ? even (x : ?)
     = if zero?(x) then 1 else (odd -(x,1))
      ? odd (x : ?)
       = if zero?(x) then 0 else (even -(x,1))
 in (odd 13)

;; even : int -> int
;; odd  : int -> int
;; (odd 13) : int

letrec ? even (odd : ?)
      = proc (x) if zero?(x)
      then 1
      else (odd -(x,1))

     in letrec ? odd (x : ?) =
       if zero?(x)
       then 0
      else ((even odd) -(x,1))
    in (odd 13)
;; even : (int -> int) -> (int -> int)
;; odd  : (int -> int)
;; (odd 13) : int




