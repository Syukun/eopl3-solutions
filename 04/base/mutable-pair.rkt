#lang eopl
;; multpair? : SchemeVal -> Bool
(define multipair?
  (lambda (v)
    (reference? v)))

;; makepair : ExpVal * ExpVal -> MutPair
(define make-pair
  (lambda (val1 val2)
    (let [(ref1 (newref val1))]
      (let [(ref2 (newref val2))]
        ref1))))

;; left : MutPair -> ExpVal
(define left
  (lambda (p)
    (deref p)))

;; right : MutPair -> ExpVal
(define right
  (lambda (p)
    (deref (+ p 1))))

;; setleft : MutPair * ExpVal -> Unspecified
(define setleft
  (lambda (p val)
    (setref! p val)))

;; setright : MutPair * ExpVal -> Unspecified
(define setright
  (lambda (p val)
    (setref! (+ p 1) val)))

