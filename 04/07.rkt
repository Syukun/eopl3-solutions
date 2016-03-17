;; Modify the rule.
(value-of exp1 env state0)  ==>  (l state1)
(value-of (deref-exp l) env state1) ==> (ref state1)
(value-of exp2 env state1) ==> (val1 state2)

(value-of (setref exp1 exp2) env state0) ==> (ref state2)
