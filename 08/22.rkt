#lang eopl
module equality-maker
 interface
  ((ints : [ opaque t
             zero : t
             succ : (t -> t)
             is-zero : (t -> bool)])
   => [ equal : (from ints take t
                      -> (from ints take t
                               -> bool))])
body
[ equal = let p = form ints take pred
          in let z? = from ints take is-zero
          in let s = from ints take succ
          in let t = from ints take t
          in letrec t equal-proc (x : t)
                        proc (y : t)
                       if z?(x) then ;; 思想确实非常简单，比较x 和 y 是否相等，两者不断减 1
                                     if z?(y) then true else false
                                else
                                     if z?(y) then false else ((equal-proc (p x)) (p y))
]
