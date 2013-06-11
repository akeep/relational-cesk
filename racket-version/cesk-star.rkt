#lang racket

(require rackunit)

;;; Important: lists contain locations, not values.  Values are
;;; substituted for the addresses at the end of eval-exp.  Since
;;; locations are represented as numbers, this means numbers cannot
;;; appear as values with a list.  It is probably possible to get
;;; around this restriction using tagging.  Since this is sufficient
;;; for implementing quines, I'm not going to worry about this
;;; limitation right now.

(define answer cons)

; this is a bad way to do this becaus it potentially assigns the
; same address to different environments in
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
  (lambda (p a s^ k*^)
    (match p
      [`(closure ,x ,body ,env)
       (let ((loc (new-loc s^)))
         (let ((env^ (ext-env x loc env)))
           (let ((s^^ (ext-s loc a s^)))
             (eval-exp-aux body env^ s^^ k*^))))]
      [`(continuation ,k*)
       (apply-k* k* (answer a s^))])))


(define make-continuation
  (lambda (k*)
    `(continuation ,k*)))


(define apply-k*
  (lambda (k* v/s)
    (printf "applying k: ~s\n" (apply-s (cdr v/s) k*))
    (match (apply-s (cdr v/s) k*)
      [`(empty-k) v/s]
      [`(call/cc-k ,k*)
       (let ((p (car v/s)) (s^ (cdr v/s)))
         (apply-proc p (make-continuation k*) s^ k*))]
      [`(throw-k ,v-e ,env^)
       (let ((cc (car v/s))
             (s (cdr v/s)))
         (match cc
           [`(continuation ,k*) (eval-exp-aux v-e env^ s k*)]
           [_ (error 'apply-k "attempt to throw non-continuation" cc)]))]
      [`(if-k ,c ,a ,env ,k*)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (if v
             (eval-exp-aux c env s k*)
             (eval-exp-aux a env s k*)))]
      [`(zero?-k ,k*)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (apply-k* k* (answer (zero? v) s)))]
      [`(sub1-k ,k*)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (apply-k* k* (answer (sub1 v) s)))]
      [`(subtraction-inner-k ,v1 ,k*)
       (let ((v2 (car v/s))
             (s (cdr v/s)))
         (apply-k* k* (answer (- v1 v2) s)))]
      [`(subtraction-outer-k ,e2 ,env ,k*)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (let ([loc (new-loc s)])
           (eval-exp-aux e2 env
             (ext-s loc (subtraction-inner-k v k*) s)
             loc)))]
      [`(addition-inner-k ,v1 ,k*)
       (let ((v2 (car v/s))
             (s^^ (cdr v/s)))
         (apply-k* k* (answer (+ v1 v2) s^^)))]
      [`(addition-outer-k ,e2 ,env ,k*)
       (let ((v1 (car v/s))
             (s^ (cdr v/s)))
         (let ([loc (new-loc s^)])
           (eval-exp-aux e2 env
             (ext-s loc (addition-inner-k v1 k*) s^)
             loc)))]
      [`(multiplication-inner-k ,v1 ,k*)
       (let ((v2 (car v/s))
             (s^^ (cdr v/s)))
         (apply-k* k* (answer (* v1 v2) s^^)))]
      [`(multiplication-outer-k ,e2 ,env ,k*)
       (let ((v1 (car v/s))
             (s^ (cdr v/s)))
         (let ([loc (new-loc s^)])
           (eval-exp-aux e2 env
             (ext-s loc (multiplication-inner-k v1 k*) s^)
             loc)))]
      [`(set!-k ,x ,env ,k*)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (let ((loc (apply-env env x)))
           (apply-k* k* (answer (void) (ext-s loc v s^)))))]
      [`(begin-inner-k ,k*)
       (let ((v2 (car v/s))
             (s^^ (cdr v/s)))
         (apply-k* k* (answer v2 s^^)))]
      [`(begin-outer-k ,rand2 ,env ,k*)
       (let ((v1 (car v/s))
             (s^ (cdr v/s)))
         (let ([loc (new-loc s^)])
           (eval-exp-aux rand2 env
             (ext-s loc (begin-inner-k k*) s^)
             loc)))]
      [`(application-inner-k ,p ,k*)
       (let ((a (car v/s))
             (s^^ (cdr v/s)))
         (apply-proc p a s^^ k*))]
      [`(application-outer-k ,rand ,env ,k*)
       (let ((p (car v/s))
             (s^ (cdr v/s)))
         (let ([loc (new-loc s^)])
           (eval-exp-aux rand env
             (ext-s loc (application-inner-k p k*) s^)
             loc)))]
      [`(list-aux-inner-k ,loc ,k*)
       (let ((loc* (car v/s))
             (s^^ (cdr v/s)))
         (apply-k* k* (answer (cons loc loc*) s^^)))]
      [`(list-aux-outer-k ,e* ,env ,k*)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (let ((loc (new-loc s^)))
           (let ((s^^ (ext-s loc v s^)))
             (let ([k-loc (new-loc s^^)])
               (list-aux (cdr e*) env
                 (ext-s k-loc (list-aux-inner-k loc k*) s^^)
                 k-loc)))))]
      [_ (error 'apply-k* "unknown continuation type ~s ~s" k* (cdr v/s))])))

(define empty-k '(empty-k))

(define if-k
  (lambda (c a env k*)
    `(if-k ,c ,a ,env ,k*)))

(define zero?-k
  (lambda (k*)
    `(zero?-k ,k*)))

(define sub1-k
  (lambda (k*)
    `(sub1-k ,k*)))

(define subtraction-inner-k
  (lambda (v1 k*)
    `(subtraction-inner-k ,v1 ,k*)))

(define subtraction-outer-k
  (lambda (e2 env k*)
    `(subtraction-outer-k ,e2 ,env ,k*)))

(define call/cc-k
  (lambda (k*)
    `(call/cc-k ,k*)))

(define throw-k
  (lambda (v-e env)
    `(throw-k ,v-e ,env)))

(define addition-inner-k
  (lambda (v1 k*)
    `(addition-inner-k ,v1 ,k*)))

(define addition-outer-k
  (lambda (e2 env k*)
    `(addition-outer-k ,e2 ,env ,k*)))

(define multiplication-inner-k
  (lambda (v1 k*)
    `(multiplication-inner-k ,v1 ,k*)))

(define multiplication-outer-k
  (lambda (e2 env k*)
    `(multiplication-outer-k ,e2 ,env ,k*)))

(define set!-k
  (lambda (x env k*)
    `(set!-k ,x ,env ,k*)))

(define begin-inner-k
  (lambda (k*)
    `(begin-inner-k ,k*)))

(define begin-outer-k
  (lambda (rand2 env k*)
    `(begin-outer-k ,rand2 ,env ,k*)))

(define application-inner-k
  (lambda (p k*)
    `(application-inner-k ,p ,k*)))

(define application-outer-k
  (lambda (rand env k*)
    `(application-outer-k ,rand ,env ,k*)))

(define list-aux-inner-k
  (lambda (loc k*)
    `(list-aux-inner-k ,loc ,k*)))

(define list-aux-outer-k
  (lambda (e* env k*)
    `(list-aux-outer-k ,e* ,env ,k*)))


(define valid-keyword?
  (lambda (kw env)
    (lambda (x)
      (and (eq? x kw) (not-in-env kw env)))))

(define eval-exp-aux
  (lambda (exp env s k*)
    (match exp
      ((? number? n)
       (apply-k* k* (answer n s)))
      ((? boolean? b)
       (apply-k* k* (answer b s)))
      ((? symbol? x)
       (apply-k* k* (answer (lookup env s x) s)))
      (`(,(? (valid-keyword? 'quote env) _) ,datum)
       (apply-k* k* (answer datum s)))
      (`(,(? (valid-keyword? 'if env) _) ,t ,c ,a)
       (let ([loc (new-loc s)])
         (eval-exp-aux t env (ext-s loc (if-k c a env k*) s) loc)))
      (`(,(? (valid-keyword? 'zero? env) _) ,e)
        (let ([loc (new-loc s)])
          (eval-exp-aux e env (ext-s loc (zero?-k k*) s) loc)))
      (`(,(? (valid-keyword? 'sub1 env) _) ,e)
        (let ([loc (new-loc s)])
          (eval-exp-aux e env (ext-s loc (sub1-k k*) s) loc)))
      (`(,(? (valid-keyword? '- env) _) ,e1 ,e2)
        (let ([loc (new-loc s)])
          (eval-exp-aux e1 env (ext-s loc (subtraction-outer-k e2 env k*) s) loc)))
      (`(,(? (valid-keyword? '+ env) _) ,e1 ,e2)
        (let ([loc (new-loc s)])
          (eval-exp-aux e1 env (ext-s loc (addition-outer-k e2 env k*) s) loc)))
      (`(,(? (valid-keyword? '* env) _) ,e1 ,e2)
        (let ([loc (new-loc s)])
          (eval-exp-aux e1 env (ext-s loc (multiplication-outer-k e2 env k*) s) loc)))
      (`(,(? (valid-keyword? 'call/cc env) _) ,e)
        (let ([loc (new-loc s)])
          (eval-exp-aux e env (ext-s loc (call/cc-k k*) s) loc)))
      (`(,(? (valid-keyword? 'throw env) _) ,cc-e ,v-e)
        (let ([loc (new-loc s)])
          (eval-exp-aux cc-e env (ext-s loc (throw-k v-e env) s) loc)))
      (`(,(? (valid-keyword? 'letcc env) _) ,cc ,body)
       (let ((loc (new-loc s)))
         (let ((env^ (ext-env cc loc env)))
           (let ((s^ (ext-s loc (make-continuation k*) s)))
             (eval-exp-aux body env^ s^ k*)))))
      (`(,(? (valid-keyword? 'lambda env) _) (,x) ,body)
       (apply-k* k* (answer (make-proc x body env) s)))
      (`(,(? (valid-keyword? 'set! env) _) ,x ,rhs)
        (let ([loc (new-loc s)])
          (eval-exp-aux rhs env (ext-s loc (set!-k x env k*) s) loc)))
      (`(,(? (valid-keyword? 'begin env) _) ,rand1 ,rand2)
        (let ([loc (new-loc s)])
          (eval-exp-aux rand1 env (ext-s loc (begin-outer-k rand2 env k*) s) loc)))
      (`(,(? (valid-keyword? 'list env) _) . ,e*)
       (list-aux e* env s k*))
      (`(,rator ,rand)
        (let ([loc (new-loc s)])
          (eval-exp-aux rator env (ext-s loc (application-outer-k rand env k*) s) loc))))))

(define list-aux
  (lambda (e* env s k*)
    (cond
      [(null? e*) (apply-k* k* (answer '() s))]
      [else
        (let ([loc (new-loc s)])
          (eval-exp-aux (car e*) env
            (ext-s loc (list-aux-outer-k e* env k*) s)
            loc))])))

(define eval-exp
  (lambda (exp env s k*)
    (match (eval-exp-aux exp env s k*)
      [`(,v . ,s^) (walk*-v v s^)])))

(define cesk-eval
  (lambda (exp)
    (let ([loc (new-loc empty-s)])
      (eval-exp exp empty-env (ext-s loc empty-k empty-s) loc))))

(define walk*-v
  (lambda (v s)
    (match v
      [(? symbol? x) x] ; quoted symbol
      [(? boolean? b) b]
      [(? number? n) n]
      [`() '()] ; empty list (created with either quote or list--doesn't matter)
      [`(,(? (lambda (x)
               (and (not (number? x))
                    (not (eq? 'closure x))
                    (not (eq? 'continuation x))))
            a) . ,d) ; quoted list (case 1) [can't overlap with a list of nums]
       `(,a . ,d)]
      [`((,aa . ,ad) . ,d) ; quoted list (case 2) [can't overlap with a list of nums]
       `((,aa . ,ad) . ,d)]
      [`(closure ,x ,body ,env)
;;; arguably I should walk* the body as well, although this could cause its own problems.
;;; although if procedures are opaque, the user really has no right to look inside
       `(closure ,x ,body ,env)]
      [`(continuation ,k*)
;;; arguably should also walk components of continuations that might contain values
        (apply-s s k*)]
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

(define cesk-tests
  (test-suite
    "tests for the cesk* implementation (from the cesk implementation)"

    (test-case
      "supporting procedure tests"

      (check-equal?
        (let ((env (ext-env 'a (new-loc empty-s) empty-env))
               (s (ext-s (new-loc empty-s) 7 empty-s)))
          (lookup env s 'a))
        7
        "lookup")

      (check-equal?
        (let ((env (ext-env 'a (new-loc empty-s) empty-env))
               (s (ext-s (new-loc empty-s) 'foo empty-s)))
          (lookup env s 'a))
        'foo
        "lookup-2"))

    (test-case
      "tests for the cesk evaluation (from scheme-version tests)"

      (check-equal?
        (cesk-eval '5)
        5
        "cesk-number")

      (check-equal?
        (cesk-eval '#t)
        #t
        "cesk-boolean")

      (check-equal?
        (let ([k-loc (new-loc empty-s)])
          (let ([s (ext-s k-loc empty-k empty-s)])
            (let ([a-loc (new-loc s)])
              (eval-exp 'a
                (ext-env 'a a-loc empty-env)
                (ext-s a-loc 7 s)
                k-loc))))
        7
        "cesk-variable")

      (check-equal?
        (let ([k-loc (new-loc empty-s)])
          (let ([s (ext-s k-loc empty-k empty-s)])
            (let ([a-loc (new-loc s)])
              (eval-exp 'a
                (ext-env 'a a-loc empty-env)
                (ext-s a-loc 'foo s)
                k-loc))))
        'foo
        "cesk-variable-2")

      (check-equal?
        (cesk-eval '((lambda (x) x) 5))
        5
        "cesk-identity")

      (check-equal?
        (cesk-eval '((lambda (x) x) (quote foo)))
        'foo
        "cesk-identity-2")

      (check-equal?
        (cesk-eval '(letcc k k))
        empty-k
        "letcc/throw-0")

      (check-equal?
        (cesk-eval '(letcc k 1))
        '1
        "letcc/throw-0b")

      (check-equal?
        (cesk-eval '(letcc k (throw k 1)))
        '1
        "letcc/throw-0c")

      (check-equal?
        (cesk-eval '(letcc k (* 5 (throw k (* 2 6)))))
        '12
        "letcc/throw-1")

      (check-equal?
        (cesk-eval '(letcc k
                      ((quote 5)
                        (throw k (quote 7)))))
        '7
        "letcc/throw-2")

      (check-equal?
        (cesk-eval '((lambda (x) (begin (set! x 5) x)) 6))
        5
        "cesk-set!")

      (check-equal?
        (cesk-eval '(quote (lambda (x) 5)))
        '(lambda (x) 5)
        "cesk-quote")

      (check-equal?
        (cesk-eval '(quote (lambda (x) x)))
        '(lambda (x) x)
        "cesk-quote-2")

      (check-equal?
        (cesk-eval '(zero? ((lambda (x) x) 0)))
        '#t
        "cesk-zero?-1")

      (check-equal?
        (cesk-eval '(zero? ((lambda (x) x) 1)))
        '#f
        "cesk-zero?-2")

      (check-equal?
        (cesk-eval '(- ((lambda (x) x) 7) ((lambda (x) x) 4)))
        '3
        "cesk-subtraction")

      (check-equal?
        (cesk-eval '(+ ((lambda (x) x) 7) ((lambda (x) x) 4)))
        '11
        "cesk-addition")

      (check-equal?
        (cesk-eval '(* ((lambda (x) x) 7) ((lambda (x) x) 4)))
        '28
        "cesk-multiplication")

      (check-equal?
        (cesk-eval
          '(if (zero? (- 7 4))
               ((lambda (x) x) (list (quote foo) (quote bar)))
               ((lambda (x) x) (list #f #t))))
        '(#f #t)
        "cesk-if-1")

      (check-equal?
        (cesk-eval
          '(if (zero? (- 6 (* 2 3)))
               ((lambda (x) x) (list (quote foo) (quote bar)))
               ((lambda (x) x) (list #f #t))))
        '(foo bar)
        "cesk-if-2")

      (define fact-five
        '((lambda (f)
            ((f f) 5))
           (lambda (f)
             (lambda (n)
               (if (zero? n)
                   1
                   (* n ((f f) (sub1 n))))))))

      (check-equal?
        (cesk-eval fact-five)
        120
        "cesk-fact-5")

      (check-equal?
        (cesk-eval '(list))
        '()
        "cesk-list-0")

      (check-equal?
        (cesk-eval '(list 5))
        '(5)
        "cesk-list-1")

      (check-equal?
        (cesk-eval '(list 5 6))
        '(5 6)
        "cesk-list-2")

      (check-equal?
        (cesk-eval
          '(list
             (zero? (- 6 (* 2 3)))
             ((lambda (x) x) (list (quote foo) (quote bar)))
             ((lambda (x) x) (list #f #t))))
        '(#t (foo bar) (#f #t))
        "cesk-list-3")

      (check-equal?
        (cesk-eval '(list (quote foo)))
        '(foo)
        "cesk-list-1a")

      (check-equal?
        (cesk-eval '(list (quote foo) (quote bar)))
        '(foo bar)
        "cesk-list-2a")

      (check-equal?
        (cesk-eval
          '(list
             (quote baz)
             ((lambda (x) x) (list (quote foo) (quote bar)))
             ((lambda (x) x) (list (quote quux)))))
        '(baz (foo bar) (quux))
        "cesk-list-3a")

      (check-equal?
        (cesk-eval '((lambda (sub1) (sub1 3)) (lambda (n) (* n n))))
        9
        "cesk-shadowing")

      (check-equal?
        (cesk-eval '((lambda (x)
                       ((lambda (quote)
                          (quote x))
                         (lambda (y) (list y y y))))
                      (quote bar)))
        '(bar bar bar)
        "cesk-shadowing-2")

      (check-equal?
        (cesk-eval '(call/cc (lambda (k) 20)))
        20
        "call/cc-1")

      (check-equal?
        (cesk-eval '(call/cc (lambda (k) (k 20))))
        20
        "call/cc-2")

      (check-equal?
        (cesk-eval '(call/cc (lambda (k) (* 5 4))))
        (call/cc (lambda (k) (* 5 4)))
        "call/cc-3")

      (check-equal?
        (cesk-eval '(call/cc (lambda (k) (k (* 5 4)))))
        (call/cc (lambda (k) (k (* 5 4))))
        "call/cc-4")

      (check-equal?
        (cesk-eval '(call/cc (lambda (k) (* 5 (k 4)))))
        (call/cc (lambda (k) (* 5 (k 4))))
        "call/cc-5")

      (check-equal?
        (cesk-eval '(+ 2 (call/cc (lambda (k) (* 5 (k 4))))))
        (+ 2 (call/cc (lambda (k) (* 5 (k 4)))))
        "call/cc-6")

      (check-equal?
        (cesk-eval '(((call/cc (lambda (k) k)) (lambda (x) x)) 1))
        (((call/cc (lambda (k) k)) (lambda (x) x)) 1)
        "call/cc-7")

      (define quinec
        '((lambda (x)
            (list x (list (quote quote) x)))
           (quote
             (lambda (x)
               (list x (list (quote quote) x))))))

      (check-equal?
        (cesk-eval quinec)
        quinec
        "cesk-quinec"))))

(provide (all-defined-out))


