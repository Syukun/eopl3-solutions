#lang eopl
;; 这道题目很有意思，那就是要求我们实现不按照顺序的赋值操作
(require "./base/data-structure.rkt")
(require "./base/parse.rkt")
(require "./base/simple-module.rkt")
;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (m-defns body) ;; 先将一些module的定义加载进入env
                 (value-of body
                           (add-module-defns-to-env m-defns (empty-env)))))))

;; add-module-defns-to-env : Listof(Defn) * Env -> Env
(define add-module-defns-to-env
  (lambda (defns env)
    (if (null? defns)
        env
        (cases module-definition (car defns)
          (a-module-definition (m-name iface m-body) ;; 好吧,这就是一个module的名字,然后是声明的变量,最后是实现
                               (add-module-defns-to-env ;; 先加载一个module,然后加载余下的module,好吧,这就是所谓的递归
                                (cdr defns)
                                (extend-env-with-module
                                 m-name ;; module的名字
                                 (value-of-module-body m-body env) ;; module里面包含的东西
                                 env)))))))
;; value-of-module-body : ModuleBody * Env -> TypedModule
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body m-body
      (defns-module-body (defns) ;; 这里的defns应该是一个list
        (simple-module
         (defns-to-env defns env))))))

;; defns-to-env : Listof(Defn) * Env -> Env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env)
        (cases definition (car defns)
          (val-defn (var exp) ;; 好吧,这个东西实在太厉害了
                    (let ([val (value-of exp env)])
                      (let ([new-env (extend-env var val env)])
                        (extend-env var val
                                    (defns-to-env ;; 递归调用
                                      (cdr defns) new-env)))))))))



;; type-of-program : Program -> Type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (module-defns body)
                 (type-of body
                          (add-module-defns-to-tenv module-defns (empty-tenv)))))))

;; add-module-defns-to-tenv : Listof(ModuleDefn) * Tenv -> Tenv
(define add-module-defns-to-tenv ;; 这个函数就是往tenv中添加类型信息
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases module-definition (car defns)
               (a-module-definition (m-name expected-iface m-body) ;; 好吧，模块的名字，预料的interface
                                    (let ((actual-iface (interface-of m-body tenv)))
                                      (if (<:-iface actual-iface expected-iface tenv)
                                          (let ((new-tenv
                                                 (extend-tenv-with-module
                                                  m-name
                                                  expected-iface
                                                  tenv)))
                                            (add-module-defns-to-tenv
                                             (cdr defns) new-tenv))
                                          (report-module-doesnt-satisfy-iface
                                           m-name expected-iface actual-iface))))))))
(define report-module-doesnt-satisfy-iface
  (lambda (m-name expected-type actual-type)
    (eopl:pretty-print
     (list 'error-in-defn-of-module: m-name
           'expected-type: expected-type
           'actual-type: actual-type))
    (eopl:error 'type-of-module-defn)))


;; interface-of : ModuleBody * Tenv -> Iface
(define interface-of
  (lambda (m-body tenv)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-iface ;; 这是一个数据类型,在iface里面
         (defns-to-decls defns tenv))))))

;; defns-to-decls : Listof(Defn) * Tenv -> Listof(Decl)
(define defns-to-decls
  (lambda (defns tenv)
    (if (null? defns)
        '()
        (cases definition (car defns)
          (val-defn (var-name exp)
                    (let ([ty (type-of exp tenv)])
                      (cons
                       (val-decl var-name ty) ;; val-decl也是一个数据类型,表示一个定义的东西
                       (defns-to-decls
                         (cdr defns)
                         (extend-tenv var-name ty tenv)))))))))
;; <:-iface : Iface * Iface * Tenv -> Bool
(define <:-iface
  (lambda (iface1 iface2 tenv)
    (cases interface iface1
      (simple-iface (decls1)
                    (cases interface iface2
                      (simple-iface (decls2)
                                    (<:-decls decls1 decls2 tenv)))))))

(define search-var-in-decls
  (lambda (name decls)
         (if (null? decls) #f
             (let ([name1 (decl->name (car decls))])
               (if (eqv? name name1)
                   (car decls)
                   (search-var-in-decls name (cdr decls)))))))
(define remove-decl
  (lambda (name decls)
    (if (null? decls)
        '()
        (let ([name1 (decl->name (car decls))])
          (if (eqv? name name1)
              (remove-decl name (cdr decls))
              (cons (car decls) (remove-decl name (cdr decls))))))))
;; <:-decls : Listof(Decl) * Listof(Decl) * Tenv -> Bool
;; 估计要改的东西就是这个啦。
(define <:-decls
  (lambda (decls1 decls2 tenv)
    (cond
      [(null? decls2) #t] ;; decls2中声明的东西应该全部实现
      [(null? decls1) #f] ;; 如果decls2不为null,而decls1为null了,显然decls2中声明的东西没有全部实现
      [else
       (let ([name1 (decl->name (car decls1))])
         (let ([maybe-decl
                (search-var-in-decls name1 decls2)])
         (if maybe-decl
             (and
              (equal?
               (decl->type (car decls1))
               (decl->type maybe-decl))
              (<:-decls (cdr decls1) (remove-decl name1 decls2) tenv))
             (eopl:error "var ~a not found!\n" name1))))])))

(define type-check
  (lambda (ast)
    (if (type-of-program ast) #t #f)))

(define run
  (lambda (string)
    (let ([ast (scan&parse string)])
      (if (type-check ast) ;; 首先要对程序进行类型检查
          (value-of-program ast)
          (eopl:error "There are something wrong with your program!\n")))))

;; test code





