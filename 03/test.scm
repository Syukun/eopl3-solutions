(define (demo var env)
  (let* [(helper
	 (lambda (x new-env)
	   (if (null? x) new-env
	       (helper (cdr x) new-env))))]
    (helper (list 1 2 3) (list 1 2 3))))
