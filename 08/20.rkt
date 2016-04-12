#lang eopl
module sum-prod-maker
 interface
  ((ints : [ opaque t
             zero : t
             succ : t
             pred : t
             is-zero : (t -> bool)])
   => [ puls : (from ints take t
                     -> (from ints take t
                              -> from ints take t))
        times : (from ints take t
                      -> (from ints take t
                               -> from int take t))])
  body
  [ plus = let t = from ints take t
            in let z? = from ints take is-zero
            in let p = from ints take pred
            in let s = from ints take succ
            in letrec t sum-proc (x : t)
                          proc (y : t)
                            if z?(x) then y else ;; 这个东西的思想其实非常简单，就是一个参数不断增加，一个参数不断减小
                                    ((sum-proc (p x)) (s y))
            in sum-proc
    times = let t = form ints take t
            in let z? = from ints take is-zero
            in let p = from ints take pred
            in let s = from ints take succ
            in letrec t times-proc (x : t)
                          proc (y : t) 
                        if z?(p x) then y else ;; 思想也很简单，那就是一边加，一边减
                        ((times-proc (p x)) ((plus y) y))
             in times-proc
]
