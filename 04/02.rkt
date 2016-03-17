;; Write down the specification of a zero?-exp
          (value-of exp1 env state0)  ==> (val1 state1)
(value-of (zero?-exp exp1) env state0) ==> #t ---> if (expval->bool val1) = 0
                                       ==> #f ---> ...

