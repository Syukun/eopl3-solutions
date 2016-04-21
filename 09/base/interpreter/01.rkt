#lang eopl
(define identifier? symbol?)









(define run
  (lambda (string)
    (value-of-program (scan&parse string))))
;; 实现了一个queue
(run "
class queue extends object
 field q
 method initialize ()
  set q = list (1, 2)
 method empty ()
  empty? (q)
 method enqueue (v)
  cons (v, q)
 method dequeue ()
  let a = car (q)
  in begin
  set q = cdr(q) ;
  a end

 let a = new queue()
 in let b = send a dequeue ()
 in let c = send a dequeue ()
 in send a empty ()
")

;; 第二个要求是扩展这个queue，加一个计数器，记录操作数
(run "
class queue extends object
 field q
 method initialize ()
  set q = list (1, 2)
 method empty ()
  empty? (q)
 method enqueue (v)
  cons (v, q)
 method dequeue ()
  let a = car (q)
  in begin
  set q = cdr(q) ;
  a end

 class queue2 extends queue
  field count
  method initialize ()
   begin
    super  initialize ();
    set count = 0
   end
  method enqueue (a-val)
    begin
    super enqueue (a-val);
    set count = -(count, -1)
    end
  method dequeue ()
    let v = super dequeue ()
    in  begin
    set count = -(count, -1);
    v
    end
  method getcount()
    count

  let a = new queue2()
  in
     begin
      send a enqueue (3);
      send a getcount ()
    end
")

;; 
