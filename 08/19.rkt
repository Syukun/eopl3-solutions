#lang eopl
module from-int-maker
 interface
  ((ints : [opaque t
            zero : t
            succ : (t -> t)
            pred : (t -> t)
            is-zero : (t -> bool)])
   => [from-int : (int -> from ints take t)])
  body
 [ from-int = let z? = from ints take is-zero
              in let z = from ints take z
              in let s = from ints take succ
              in let p = from ints take pred
              in letrec from ints take t from-int (x : int)
                        = if (z? x)
                          then z
                          else (s (from-int -(x, 1)))]
;; 好吧，差不多就是这样啦！
