#lang eopl
;; determine whether each of the following expression is simple?
;; 什么叫做simple?
-((f -(x, 1)), 1)
;--> not simple

(f -(-(x, y), 1))
;--> simple

if zero?(x) then -(x, y) else -(-(x, y), 1)
;--> simple-exp

let x = proc (y) (y x) in -(x, 3)
;--> not simple-exp

let f = proc (x) x in (f 3)
;--> simple-exp
