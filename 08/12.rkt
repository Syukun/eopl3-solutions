#lang eopl
;; Could the definition of and and not be moved from inside the moduleto outside it?
;; What about to-bool?
module mybool
  interface
   [ opaque t
     true : t
     false : t
     and : (t -> (t -> t))
     not : (t -> t)
     to-bool : (t -> bool)]
   body
    [ type t = int
      true = 0
      false = 13
      and = proc (x : t)
             proc (y : t)
              if zero?(x) then y else false
      not = proc (x : t)
              if zero?(x) then false else true
      to-bool = proc(x : t) zero?(x)]

   let true = from mybool take true
   in let false = from mybool take false
   in let and = from mybool take and
   in ((and true) false)

;; 我的答案是不能，都不能，原因很简单，因为and和not的实现是依赖于body中的type t = int的
;; 如果将它们移出了module，这个abstract boundary的含义也就不是很大了。

