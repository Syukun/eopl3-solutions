#lang eopl
(require "parse.rkt")
(require "interpreter.rkt")
(require "translator.rkt")
(require "helper.rkt")

(define value-of-translation
  (lambda (pgm)
    (cases program pgm
           (a-program (exp1)
		      (begin
			(print "value-of-translation : exp1 --> " exp1)
			(value-of exp1 (init-nameless-env)))))))

(define (trans prg)
  (translation-of-program
   (scan&parse prg)))

(define run
  (lambda (string)
    (value-of-translation
     (let [(translated-result
	    (translation-of-program ;; It's very funny to see the run procedure
	     (scan&parse string)))] 
       (begin
         (print "run : translated-result --> " translated-result)
	 translated-result)))
    ))

;; translated函数输出翻译后的信息
(define (translated string)
  (translation-of-program
	     (scan&parse string)))
;; test code
(run "unpack x y = cons(1, cons(3, emptylist)) in -(x, y)")