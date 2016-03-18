#lang eopl
;; Write the rule for let.

(value-of exp1 env state0) ==> (val1 state1)
(value-of (let-exp  var exp1 let-body) env statee0) ==> (value-of let-body [var = l] env [l = val1]  state1)
                                                       ==> (val2 state2)
