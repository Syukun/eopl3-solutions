;; Write down the specification for a begin expression
  (value-of exp1 env state0) ==> (val1 env state1)
  (value-of exp2 env state1) ==> (val2 env state2)
  (value-of exp3 env state2) ==> (val3 env state3)
               ... ...
  (value-of expn env staten-1) ==> (valn env staten)

(value-of (begin-exp exp1 exp2 exp3 ... expn) env state0)  ==> (valn env staten)
