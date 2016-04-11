#lang eopl


module mybool
 interface
  [ opaque t
    true : t
    false : t
    and : (t -> (t -> t))
    not : (t -> t)
    to-bool : (t -> bool) ]
  body
  [ type t = int
    true = 1
    false = 0
    and = proc (x :  t)
            proc (y : t)
             if zero?(x) then false else y

    not = proc (x : t)
           if zero?(x) then true else false

    to-bool = proc (x : t)
               if zero?(x) then zero?(1) else zero?(0) ]

let true = from mybool take true
in let false = from mybool take false
in let and = from mybool take and
in ((and true) false)

;; 这段代码返回的结果是(num-val 0)
;; 我们也看得很真切。不过话说题目到底是个什么意思？
