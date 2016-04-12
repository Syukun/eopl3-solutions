#lang eopl
;; write a module procedure that takes an implementation of arithemetic ints and produces antoher
;; implementation of arithmetic in which the number k is representation of 2 * k in ints
module m
interface
 ((ints : [ opaque t
            zero : t
            succ : (t -> t)
            pred : (t -> t)
            is-zero : (t -> bool)])
  => [ zero : t
       succ : (t -> t)
       pred : (t -> t)
       is-zero : (t -> bool)])
body
[
 plus = let t = from ints take t
            in let z? = from ints take is-zero
            in let p = from ints take pred
            in let s = from ints take succ
            in letrec t sum-proc (x : t)
                          proc (y : t)
                            if z?(x) then y else ;; 这个东西的思想其实非常简单,就是一个参数不断增加,一个参数不断减小
                                    ((sum-proc (p x)) (s y))
            in sum-proc
    times = let t = form ints take t
            in let z? = from ints take is-zero
            in let p = from ints take pred
            in let s = from ints take succ
            in letrec t times-proc (x : t)
                          proc (y : t) 
                        if z?(p x) then y else ;; 思想也很简单,那就是一边加,一边减
                        ((times-proc (p x)) ((plus y) y))
            in times-proc
     two = let s = from ints take succ
           in let z = from ints take zero
           (pred (pred z))

 zero = from ints take zero;; zero这个函数不变
 is-zero = from ints take is-zero ;; 自然 is-zero 这个函数也不变
 pred = let p = from ints take pred ;; pred表示为(2 * k)这里的k 是前一个ints的pred
        let t = from ints take t
        letrec t pred-proc (x : t)
        = ((times (p x)) two)
        in pred-proc
        
 succ = let s = from ints take succ
        let t = from ints take t
        letrec t succ-proc (x : t)
         = ((times (s x)) two)
         in succ-proc
 ]
                
        

