#lang racket

(define answer cons)

(define new-loc length)

(define lookup
  (lambda (env s x)
    (let ((loc (apply-env env x)))
      (apply-s s loc))))

(define apply-env
  (lambda (env x)
    (cond
      ((assv x env) => cdr)
      (else (error 'apply-env "unbound variable ~s" x)))))

(define apply-s
  (lambda (s loc)
    (cond
      ((assv loc s) => cdr)
      (else (error 'apply-s "unbound location ~s" loc)))))

(define ext-env
  (lambda (x loc env)
    `((,x . ,loc) . ,env)))

(define ext-s
  (lambda (loc val s)
    `((,loc . ,val) . ,s)))

(define empty-env '())

(define empty-s '())


(define not-in-env
  (lambda (x env)
    (not (assq x env))))


(define make-proc
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define make-continuation
  (lambda (k)
    `(continuation ,k)))

(define apply-proc
  (lambda (p a s^ k^)
    (match p
      (`(closure ,x ,body ,env)
       (let ((loc (new-loc s^)))
         (let ((env^ (ext-env x loc env)))
           (let ((s^^ (ext-s loc a s^)))
             (eval-exp-aux body env^ s^^ k^)))))
      (`(continuation ,k)
       (apply-k k (answer a s^))))))


(define apply-k
  (lambda (k v/s)
    (match k
      (`(empty-k) v/s)
      (`(call/cc-k ,k)
       (let ((p (car v/s)) (s^ (cdr v/s)))
         (apply-proc p (make-continuation k) s^ k)))
      (`(set!-k ,x ,env ,k)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (let ((loc (apply-env env x)))
           (apply-k k (answer (void) (ext-s loc v s^))))))
      (`(application-inner-k ,p ,k)
       (let ((a (car v/s))
             (s^^ (cdr v/s)))
         (apply-proc p a s^^ k)))
      (`(application-outer-k ,rand ,env ,k)
       (let ((p (car v/s))
             (s^ (cdr v/s)))
         (eval-exp-aux rand env s^ (application-inner-k p k))))
      (`(list-aux-inner-k ,loc ,k)
       (let ((loc* (car v/s))
             (s^^ (cdr v/s)))
         (apply-k k (answer (cons loc loc*) s^^))))
      (`(list-aux-outer-k ,e* ,env ,k)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (list-aux (cdr e*) env s^ (list-aux-inner-k v k)))))))

(define empty-k '(empty-k))

(define call/cc-k
  (lambda (k)
    `(call/cc-k ,k)))

(define set!-k
  (lambda (x env k)
    `(set!-k ,x ,env ,k)))

(define application-inner-k
  (lambda (p k)
    `(application-inner-k ,p ,k)))

(define application-outer-k
  (lambda (rand env k)
    `(application-outer-k ,rand ,env ,k)))

(define list-aux-inner-k
  (lambda (loc k)
    `(list-aux-inner-k ,loc ,k)))

(define list-aux-outer-k
  (lambda (e* env k)
    `(list-aux-outer-k ,e* ,env ,k)))

(define valid-rator? 
  (lambda (env)
    (lambda (x)
      (not (and (memq x '(quote list call/cc)) (not-in-env x env))))))

(define valid-keyword?
  (lambda (kw env)
    (lambda (x)
      (and (eq? x kw) (not-in-env kw env)))))

(define eval-exp-aux
  (lambda (exp env s k)
    (match exp
      (`(,(? (valid-rator? env) rator) ,rand)
       (eval-exp-aux rator env s (application-outer-k rand env k)))
      (`(,(? (valid-keyword? 'lambda env) _) (,x) ,body)
       (apply-k k (answer (make-proc x body env) s)))
      ((? symbol? x)
       (apply-k k (answer (lookup env s x) s)))   
      (`(,(? (valid-keyword? 'quote env) _) ,datum)
       (apply-k k (answer datum s)))
      (`(,(? (valid-keyword? 'list env) _) . ,e*)
       (list-aux e* env s k))
      (`(,(? (valid-keyword? 'set! env) _) ,x ,rhs)
       (eval-exp-aux rhs env s (set!-k x env k)))
      (`(,(? (valid-keyword? 'call/cc env) _) ,e)
       (eval-exp-aux e env s (call/cc-k k))))))

(define eval-exp
  (lambda (exp env s k)
    (let ((v/s^ (eval-exp-aux exp env s k)))
      (car v/s^))))

(define list-aux
  (lambda (e* env s k)
    (match e*
      (`() (apply-k k (answer '() s)))         
      (`(,a . ,d)
       (eval-exp-aux a env s
                     (list-aux-outer-k e* env k))))))

(module* test #f
  (require rackunit)

  (check-eqv?
    (let ((env (ext-env 'a (new-loc empty-s) empty-env))
           (s (ext-s (new-loc empty-s) 'bar empty-s)))
      (lookup env s 'a))
    'bar
     "lookup")

  (check-eqv?
    (let ((env (ext-env 'a (new-loc empty-s) empty-env))
           (s (ext-s (new-loc empty-s) 'foo empty-s)))
      (lookup env s 'a))
    'foo
    "lookup-2")

  (check-eqv?
    (eval-exp 'a
      (ext-env 'a (new-loc empty-s) empty-env)
      (ext-s (new-loc empty-s) 'foo empty-s)
      empty-k)
    'foo
     "cesk-variable")
 
  (check-eqv?
    (eval-exp '((lambda (x) x) (quote foo))
      empty-env
      empty-s
      empty-k)
    'foo
     "cesk-identity")

  (check-eqv?
    (eval-exp '((lambda (x) ((lambda (ignore) x) (set! x (quote foo)))) (quote bar))
      empty-env
      empty-s
      empty-k)
    'foo
     "cesk-set!")

  (check-equal?
    (eval-exp '(quote (lambda (x) x))
      empty-env
      empty-s
      empty-k)
    '(lambda (x) x)
     "cesk-quote")

  (check-eqv?
    (eval-exp '(list)
      empty-env
      empty-s
      empty-k)
    '()
     "cesk-list-0")

  (check-equal?
    (eval-exp '(list (quote foo))
      empty-env
      empty-s
      empty-k)
    '(foo)
     "cesk-list-1")

  (check-equal?
    (eval-exp '(list (quote foo) (quote bar))
      empty-env
      empty-s
      empty-k)
    '(foo bar)
     "cesk-list-2")

  (check-equal?
    (eval-exp '(list (quote baz)
                 ((lambda (x) x) (list (quote foo) (quote bar)))
                 ((lambda (x) x) (list (quote quux))))
      empty-env
      empty-s
      empty-k)
    '(baz (foo bar) (quux))
     "cesk-list-3a")

  (check-eqv?
    (eval-exp '((lambda (quote) (quote quote)) (lambda (x) (quote bar)))
      empty-env
      empty-s
      empty-k)
    'bar
     "cesk-shadowing")

  (check-equal?
    (eval-exp '((lambda (x)
                  ((lambda (quote)
                     (quote x))
                    (lambda (y) (list y y y))))
                 (quote bar))
      empty-env
      empty-s
      empty-k)
    '(bar bar bar)
     "cesk-shadowing-2")


  (check-eqv?
    (eval-exp '(call/cc (lambda (k) (quote foo)))
      empty-env
      empty-s
      empty-k)
    'foo
     "call/cc-1")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k) (k (quote foo))))
      empty-env
      empty-s
      empty-k)
    'foo
     "call/cc-2")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k)
                          ((lambda (x) x) (quote foo))))
      empty-env
      empty-s
      empty-k)
    'foo
     "call/cc-3")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k)
                          (k ((lambda (x) x) (quote foo)))))
      empty-env
      empty-s
      empty-k)  
    'foo
     "call/cc-4")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k)
                          ((lambda (x) (quote bar)) (k (quote foo)))))
      empty-env
      empty-s
      empty-k)  
    'foo
     "call/cc-5")

  (check-eqv?
    (eval-exp '((lambda (x) x)
                 (call/cc (lambda (k)
                            ((lambda (x) (quote bar)) (k (quote foo))))))
      empty-env
      empty-s
      empty-k)  
    'foo
     "call/cc-6")

  (check-eqv?
    (eval-exp '(((call/cc (lambda (k) k)) (lambda (x) x)) (quote foo))
      empty-env
      empty-s
      empty-k)  
    'foo
     "call/cc-7")

  (define quinec 
    '((lambda (x)
        (list x (list (quote quote) x)))
       (quote
         (lambda (x)
           (list x (list (quote quote) x))))))

  (check-equal?
    (eval-exp quinec
      empty-env
      empty-s
      empty-k)
    quinec
     "cesk-quinec"))

(provide (all-defined-out))
