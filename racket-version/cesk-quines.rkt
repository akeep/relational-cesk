#lang racket

;;; Important: lists contain locations, not values.  Values are
;;; substituted for the addresses at the end of eval-exp.  Since
;;; locations are represented as numbers, this means numbers cannot
;;; appear as values with a list.  It is probably possible to get
;;; around this restriction using tagging.  Since this is sufficient
;;; for implementing quines, I'm not going to worry about this
;;; limitation right now.

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

(define apply-proc
  (lambda (p a s^ k^)
    (match p
      [`(closure ,x ,body ,env)
       (let ((loc (new-loc s^)))
         (let ((env^ (ext-env x loc env)))
           (let ((s^^ (ext-s loc a s^)))
             (eval-exp-aux body env^ s^^ k^))))])))



(define apply-k
  (lambda (k v/s)
    (match k
      [`(empty-k) v/s]
      [`(application-inner-k ,p ,k)
       (let ((a (car v/s))
             (s^^ (cdr v/s)))
         (apply-proc p a s^^ k))]
      [`(application-outer-k ,rand ,env ,k)
       (let ((p (car v/s))
             (s^ (cdr v/s)))
         (eval-exp-aux rand env s^ (application-inner-k p k)))]
      [`(list-aux-inner-k ,loc ,k)
       (let ((loc* (car v/s))
             (s^^ (cdr v/s)))
         (apply-k k (answer (cons loc loc*) s^^)))]
      [`(list-aux-outer-k ,e* ,env ,k)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (let ((loc (new-loc s^)))
           (let ((s^^ (ext-s loc v s^)))
             (list-aux (cdr e*) env s^^ (list-aux-inner-k loc k)))))]
      [_ (error 'apply-k "unknown continuation type")])))

(define empty-k '(empty-k))

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


(define valid-keyword?
  (lambda (kw env)
    (lambda (x)
      (and (eq? x kw) (not-in-env kw env)))))


(define eval-exp-aux
  (lambda (exp env s k)
    (match exp
      ((? symbol? x)
       (apply-k k (answer (lookup env s x) s)))
      (`(,(? (valid-keyword? 'quote env) _) ,datum)
       (apply-k k (answer datum s)))
      (`(,(? (valid-keyword? 'lambda env) _) (,x) ,body)
       (apply-k k (answer (make-proc x body env) s)))
      (`(,(? (valid-keyword? 'list env) _) . ,e*)
       (list-aux e* env s k))
      (`(,rator ,rand)
       (eval-exp-aux rator env s (application-outer-k rand env k))))))

(define list-aux
  (lambda (e* env s k)
    (cond
      [(null? e*) (apply-k k (answer '() s))]         
      [else
       (eval-exp-aux (car e*) env s
                 (list-aux-outer-k e* env k))])))

(define eval-exp
  (lambda (exp env s k)
    (match (eval-exp-aux exp env s k)
      [`(,v . ,s^)
       (walk*-v v s^)])))

(define walk*-v
  (lambda (v s)
    (match v
      [(? symbol? x) x] ; quoted symbol      
      [`() '()] ; empty list (created with either quote or list--doesn't matter)
      [`(,(? (lambda (x) (and (not (number? x)) (not (eq? 'closure x)))) a) . ,d) ; quoted list (case 1) [can't overlap with a list of nums]
       `(,a . ,d)]
      [`((,aa . ,ad) . ,d) ; quoted list (case 2) [can't overlap with a list of nums]
       `((,aa . ,ad) . ,d)]
      [`(closure ,x ,body ,env)
;;; arguably I should walk* the body as well, although this could cause its own problems.
;;; although if procedures are opaque, the user really has no right to look inside
       `(closure ,x ,body ,env)]
      [`(,(? number? addr) . ,addr*) ; non-empty list
       (map-lookup-address `(,addr . ,addr*) s)])))

(define map-lookup-address
  (lambda (addr* s)
    (match addr*
      [`() '()]
      [`(,(? number? addr) . ,addr-res)
       (let ((t (apply-s s addr)))
         (let ((v (walk*-v t s)))
           (cons v (map-lookup-address addr-res s))))])))

(module* test #f
  (require rackunit)

  (check-equal?
    (let ((env (ext-env 'a (new-loc empty-s) empty-env))
           (s (ext-s (new-loc empty-s) 'foo empty-s)))
      (lookup env s 'a))
    'foo
     "lookup")

  (check-equal?
    (eval-exp 'a
      (ext-env 'a (new-loc empty-s) empty-env)
      (ext-s (new-loc empty-s) 'foo empty-s)
      empty-k)
    'foo
     "cesk-variable")

  (check-equal?
    (eval-exp '((lambda (x) x) (quote foo))
      empty-env
      empty-s
      empty-k)
    'foo
     "cesk-identity")

  (check-equal?
    (eval-exp '(quote (lambda (x) x))
      empty-env
      empty-s
      empty-k)
    '(lambda (x) x)
     "cesk-quote")

  (check-equal?
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
     "cesk-list-3")

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
     "cesk-shadowing")

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
