#lang eopl
(provide (all-defined-out))
(require "queue.rkt")

;; 先是一些全局的变量
(define the-ready-queue 'uninitialized)               ;; 就绪队列       
(define the-final-answer 'uninitialized)              ;; 最终的结果
(define the-max-time-slice 'uninitialized)            ;; 最大的时间片
(define the-time-remaining 'uninitialized)            ;; 剩余的时间

;; initialize-scheduler! : Int -> Unspecified
(define initialize-scheduler!
  (lambda (ticks)
    (set! the-ready-queue (empty-queue)) ;; 就绪队列
    (set! the-final-answer 'uninitialized)
    (set! the-max-time-slice ticks) ;; 最大的时间片
    (set! the-time-remaining the-max-time-slice))) ;; 剩余的时间

;; set-remaining-time : Int -> Unspecified
(define set-remaining-time!
  (lambda (rm)
    (set! the-time-remaining rm)))

;; place-on-ready-queue! : Thread -> Unspecified
(define place-on-ready-queue!
  (lambda (th)
    (set! the-ready-queue
          (enqueue the-ready-queue th)))) ;; 其实就是进入队列而已

;; run-next-thread : () -> FinalAnswer
(define run-next-thread
  (lambda ()
    (if (empty? the-ready-queue)
        the-final-answer
        (dequeue the-ready-queue
                 (lambda (first-ready-thread other-ready-threads)
                   (set! the-ready-queue other-ready-threads)
                   (set! the-time-remaining the-max-time-slice)
                   (first-ready-thread)))))) ;; 好吧，所谓的出队列

;; set-final-answer! : Expval -> Unspecified
(define set-final-answer!
  (lambda (val)
    (set! the-final-answer val)))

;; time-expired? : () -> Bool
(define time-expired?
  (lambda ()
           (zero? the-time-remaining)))

;; decrement-time! : () -> Unspecified
(define decrement-timer!
  (lambda ()
    (set! the-time-remaining (- the-time-remaining 1))))



        
