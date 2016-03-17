;; Write down the specification for a call-exp
(value-of exp1 env state0) ==> (val1 state1)
(value-of (call-exp exp exp1) env state0) ==> (val state2)