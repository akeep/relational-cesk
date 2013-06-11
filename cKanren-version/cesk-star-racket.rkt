#lang cKanren

(require (except-in cKanren/miniKanren fail))
(require cKanren/absento)
(require cKanren/neq)
(require cKanren/fd)

(require (only-in racket remove-duplicates))
(require rackunit)

;; shameless stolen from the racket rnrs implementation:

(define 64-bit? (fixnum? (expt 2 33)))

(define fixnum-width (if 64-bit? 63 31))

; restricted to 0 because fd constraints only support natural numbers
(define least-fixnum 0 #;(- (expt 2 (- fixnum-width 1))))

(define greatest-fixnum (- (expt 2 (- fixnum-width 1)) 1))

;; redone conversion from the Racket version of the Scheme cesk.scm code.

(define answero
  (lambda (v s ans)
    (== ans `(,v . ,s))))

(define new-loco
  (lambda (s loc)
    (fresh (loc* v*)
      (== `(,loc* ,v*) s)
      (numbero loc)
      (absento loc loc*))))

(define not-in-envo
  (lambda (x env)
    (fresh (x* loc*)
      (== `(,x* ,loc*) env)
      (symbolo x)
      (absento x x*))))

(define lookupo
  (lambda (env s x v)
    (fresh (loc)
      (apply-envo env x loc)
      (apply-so s loc v))))

(define apply-env-helpo
  (lambda (x x* loc* loc)
    (conde
      [(== '() x*) (== #f #t)]
      [(fresh (var x*^ var-loc loc*^)
         (symbolo var)
         (symbolo x)
         (numbero loc)
         (numbero var-loc)
         (== `(,var . ,x*^) x*)
         (== `(,var-loc . ,loc*^) loc*)
         (conde
           [(== var x) (== loc var-loc)]
           [(=/= var x) (apply-env-helpo x x*^ loc*^ loc)]))])))

(define apply-envo
  (lambda (env x loc)
    (fresh (x* loc*)
      (== env `(,x* ,loc*))
      (apply-env-helpo x x* loc* loc))))

(define apply-s-helpo
  (lambda (loc loc* v* v)
    (conde
      [(== loc* '()) (== #t #f)]
      [(fresh (floc val loc*^ v*^)
         (numbero loc)
         (numbero floc)
         (== `(,floc . ,loc*^) loc*)
         (== `(,val . ,v*^) v*)
         (conde
           [(== loc floc) (== v val)]
           [(=/= loc floc) (apply-s-helpo loc loc*^ v*^ v)]))])))

(define apply-so
  (lambda (s loc v)
    (fresh (loc* v*)
      (== `(,loc* ,v*) s)
      (apply-s-helpo loc loc* v* v))))

(define ext-envo
  (lambda (x loc env env^)
    (fresh (x* loc*)
      (symbolo x)
      (== `(,x* ,loc*) env)
      (== env^ `((,x . ,x*) (,loc . ,loc*))))))

(define ext-so
  (lambda (loc val s s^)
    (fresh (loc* val*)
      (numbero loc)
      (== `(,loc* ,val*) s)
      (== s^ `((,loc . ,loc*) (,val . ,val*))))))

;; it's worth it to spend the extra pair to make the environment more readable
;; in the standard printer.
(define empty-env '(() ()))

(define empty-store '(() ()))


(define make-proco
  (lambda (x body env proc)
    (== proc `(closure ,x ,body ,env))))

(define apply-proco
  (lambda (p a s^ k*^ v/s^ v-out)
    (conde
      [(fresh (x body env loc env^ s^^)
         (== p `(closure ,x ,body ,env))
         (new-loco s^ loc)
         (ext-envo x loc env env^)
         (ext-so loc a s^ s^^)
         (eval-exp-auxo body env^ s^^ k*^ v/s^ v-out))]
      [(fresh (k* ans)
         (== p `(continuation ,k*))
         (answero a s^ ans)
         (apply-k*o k* ans v/s^))])))

(define make-continuationo
  (lambda (k* cont)
    (== cont `(continuation ,k*))))

(define apply-k*o
  (lambda (k* v/s v/s^)
    (fresh (k v s)
      (== `(,v . ,s) v/s)
      (apply-so s k* k)
      (project (k)
        (prtm "applying k: ~s\n" k))
      (conde
        [(== k `(empty-k)) (== v/s^ v/s)]
        [(fresh (k*^ p s^ cont v-out-ignore)
           (== k `(call/cc-k ,k*^))
           (make-continuationo k*^ cont)
           (apply-proco v cont s k*^ v/s^ v-out-ignore))]
        [(fresh (v-e env^ cc v-out-ignore)
           (== k `(throw-k ,v-e ,env^))
           (make-continuationo cc v)
           (eval-exp-auxo v-e env^ s cc v/s^ v-out-ignore))]
        [(fresh (c a env k*^ v-out)
           (== k `(if-k ,c ,a ,env ,k*^ ,v-out))
           (conde
             [(=/= v #f) (eval-exp-auxo c env s k*^ v/s^ v-out)]
             [(== v #f) (eval-exp-auxo a env s k*^ v/s^ v-out)]))]
        [(fresh (k*^ ans v-out)
           (== k `(zero?-k ,k*^ ,v-out))
           (infd v (range least-fixnum greatest-fixnum))
           (conde
             [(=fd v 0) (== #t v-out) (answero #t s ans)]
             [(=/=fd v 0) (== #f v-out) (answero #f s ans)])
           (apply-k*o k*^ ans v/s^))]
        [(fresh (k*^ ans v^ v-out)
           (== k `(sub1-k ,k*^ ,v-out))
           (infd v v^ (range least-fixnum greatest-fixnum))
           (plusfd v^ 1 v) ;; x + 1 = y => x = y - 1
           (answero v^ s ans)
           (== v^ v-out)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (v1 k*^ ans v^ v-out)
           (== k `(subtraction-inner-k ,v1 ,k*^ ,v-out))
           (infd v1 (range least-fixnum greatest-fixnum))
           (infd v (range least-fixnum greatest-fixnum))
           (infd v^ (range least-fixnum greatest-fixnum))
           (plusfd v^ v v1)  ; y = v1 - v => y + v = v1
           (answero v^ s ans)
           (== v^ v-out)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (e2 env k*^ k^^ k*^^ s^ v-out v-out-ignore)
           (== k `(subtraction-outer-k ,e2 ,env ,k*^ ,v-out))
           (subtraction-inner-ko v k*^ v-out k^^)
           (new-loco s k*^^)
           (ext-so k*^^ k^^ s s^)
           (eval-exp-auxo e2 env s^ k*^^ v/s^ v-out-ignore))]
        [(fresh (v1 k*^ ans v^ v-out)
           (== k `(addition-inner-k ,v1 ,k*^ ,v-out))
           (infd v1 (range least-fixnum greatest-fixnum))
           (infd v (range least-fixnum greatest-fixnum))
           (infd v^ (range least-fixnum greatest-fixnum))
           (plusfd v1 v v^)
           (answero v^ s ans)
           (== v^ v-out)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (e2 env k*^ k^^ k*^^ s^ v-out v-out-ignore)
           (== k `(addition-outer-k ,e2 ,env ,k*^ ,v-out))
           (addition-inner-ko v k*^ v-out k^^)
           (new-loco s k*^^)
           (ext-so k*^^ k^^ s s^)
           (eval-exp-auxo e2 env s^ k*^^ v/s^ v-out-ignore))]
        [(fresh (v1 k*^ ans v^ v-out)
           (== k `(multiplication-inner-k ,v1 ,k*^ ,v-out))
           (infd v1 (range least-fixnum greatest-fixnum))
           (infd v (range least-fixnum greatest-fixnum))
           (infd v^ (range least-fixnum greatest-fixnum))
           (timesfd v1 v v^)
           (== v^ v-out)
           (answero v^ s ans)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (e2 env k*^ k^^ k*^^ s^ v-out v-out-ignore)
           (== k `(multiplication-outer-k ,e2 ,env ,k*^ ,v-out))
           (multiplication-inner-ko v k*^ v-out k^^)
           (new-loco s k*^^)
           (ext-so k*^^ k^^ s s^)
           (eval-exp-auxo e2 env s^ k*^^ v/s^ v-out-ignore))]
        [(fresh (x env k*^ s^ loc ans s^^ v-out)
           (== k `(set!-k ,x ,env ,k*^ ,v-out))
           (apply-envo env x loc)
           (ext-so loc v s s^)
           (answero (void) s^ ans)
           ; (== (void) v-out)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (k*^ ans)
           (== k `(begin-inner-k ,k*^))
           (answero v s ans)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (rand2 env k*^ k^^ s^ k*^^ v-out)
           (== k `(begin-outer-k ,rand2 ,env ,k*^ ,v-out))
           (begin-inner-ko k*^ k^^)
           (new-loco s k*^^)
           (ext-so k*^^ k^^ s s^)
           (eval-exp-auxo rand2 env s^ k*^^ v/s^ v-out))]
        [(fresh (p k*^ v-out)
           (== k `(application-inner-k ,p ,k*^ ,v-out))
           (apply-proco p v s k*^ v/s^ v-out))]
        [(fresh (rand env k*^ s^ k^^ k*^^ v-out v-out-ignore)
           (== k `(application-outer-k ,rand ,env ,k*^ ,v-out))
           (application-inner-ko v k*^ v-out k^^)
           (new-loco s k*^^)
           (ext-so k*^^ k^^ s s^)
           (eval-exp-auxo rand env s^ k*^^ v/s^ v-out-ignore))]
        [(fresh (v1 k*^ ans)
           (== k `(list-aux-inner-k ,v1 ,k*^))
           (answero (cons v1 v) s ans)
           (apply-k*o k*^ ans v/s^))]
        [(fresh (e* env k*^ a d k^^ k*^^ s^ v-out)
           (== k `(list-aux-outer-k ,e* ,env ,k*^ ,v-out))
           (== e* `(,a . ,d))
           (list-aux-inner-ko v k*^ k^^)
           (new-loco s k*^^)
           (ext-so k*^^ k^^ s s^)
           (list-auxo d env s^ k*^^ v/s^ v-out))]))))

(define empty-k '(empty-k))

(define if-ko
  (lambda (c a env k* v-out k^)
    (== k^ `(if-k ,c ,a ,env ,k* ,v-out))))

(define zero?-ko
  (lambda (k* v-out k^)
    (== k^ `(zero?-k ,k* ,v-out))))

(define sub1-ko
  (lambda (k* v-out k^)
    (== k^ `(sub1-k ,k* ,v-out))))

(define subtraction-inner-ko
  (lambda (v1 k* v-out k^)
    (== k^ `(subtraction-inner-k ,v1 ,k* ,v-out))))

(define subtraction-outer-ko
  (lambda (e2 env k* v-out k^)
    (== k^ `(subtraction-outer-k ,e2 ,env ,k* ,v-out))))

(define call/cc-ko
  (lambda (k* k^)
    (== k^ `(call/cc-k ,k*))))

(define throw-ko
  (lambda (v-e env k^)
    (== k^ `(throw-k ,v-e ,env))))

(define addition-inner-ko
  (lambda (v1 k* v-out k^)
    (== k^ `(addition-inner-k ,v1 ,k* ,v-out))))

(define addition-outer-ko
  (lambda (e2 env k* v-out k^)
    (== k^ `(addition-outer-k ,e2 ,env ,k* ,v-out))))

(define multiplication-inner-ko
  (lambda (v1 k* v-out k^)
    (== k^ `(multiplication-inner-k ,v1 ,k* ,v-out))))

(define multiplication-outer-ko
  (lambda (e2 env k* v-out k^)
    (== k^ `(multiplication-outer-k ,e2 ,env ,k* ,v-out))))

(define set!-ko
  (lambda (x env k* v-out k^)
    (== k^ `(set!-k ,x ,env ,k* ,v-out))))

(define begin-inner-ko
  (lambda (k* k^)
    (== k^ `(begin-inner-k ,k*))))

(define begin-outer-ko
  (lambda (rand2 env k* v-out k^)
    (== k^ `(begin-outer-k ,rand2 ,env ,k* ,v-out))))

(define application-inner-ko
  (lambda (p k* v-out k^)
    (== k^ `(application-inner-k ,p ,k* ,v-out))))

(define application-outer-ko
  (lambda (rand env k* v-out k^)
    (== k^ `(application-outer-k ,rand ,env ,k* ,v-out))))

(define list-aux-inner-ko
  (lambda (loc k* k^)
    (== k^ `(list-aux-inner-k ,loc ,k*))))

(define list-aux-outer-ko
  (lambda (e* env k* v-out k^)
    (== k^ `(list-aux-outer-k ,e* ,env ,k* ,v-out))))

(define eval-exp-auxo
  (lambda (exp env s k* v/s^ v-out)
    (fresh ()
      (absento 'continuation exp)
      (absento 'closure exp)
      (conde
        [(infd exp (range least-fixnum greatest-fixnum))
         (fresh (ans)
           (answero exp s ans)
           (== exp v-out)
           (apply-k*o k* ans v/s^))]
        [(== #t exp)
         (fresh (ans)
           (== exp v-out)
           (answero #t s ans)
           (apply-k*o k* ans v/s^))]
        [(== #f exp)
         (fresh (ans)
           (answero #f s ans)
           (== exp v-out)
           (apply-k*o k* ans v/s^))]
        [(symbolo exp)
         (fresh (ans v)
           (== v v-out)
           (lookupo env s exp v)
           (answero v s ans)
           (apply-k*o k* ans v/s^))]
        [(fresh (datum ans)
           (== exp `(quote ,datum))
           (== datum v-out)
           (not-in-envo 'quote env)
           (answero datum s ans)
           ;; here to keep eval-exp-auxo from generating continutations or
           ;; closures as quoted constants that it expects to be able to apply
           ;; (perhaps this problem could also be fixed by choosing a different
           ;; representation for these, instead of quoted lists).
           (apply-k*o k* ans v/s^))]
        [(fresh (t c a k^ k*^ s^ v-out-ignore)
           (== exp `(if ,t ,c ,a))
           (not-in-envo 'if env)
           (if-ko c a env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo t env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e k^ k*^ s^ v-out-ignore)
           (== exp `(zero? ,e))
           (not-in-envo 'zero? env)
           (zero?-ko k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo e env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e k^ k*^ s^ v-out-ignore)
           (== exp `(sub1 ,e))
           (not-in-envo 'sub1 env)
           (sub1-ko k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo e env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e1 e2 k^ k*^ s^ v-out-ignore)
           (== exp `(- ,e1 ,e2))
           (not-in-envo '- env)
           (subtraction-outer-ko e2 env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo e1 env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e1 e2 k^ k*^ s^ v-out-ignore)
           (== exp `(+ ,e1 ,e2))
           (not-in-envo '+ env)
           (addition-outer-ko e2 env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo e1 env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e1 e2 k^ k*^ s^ v-out-ignore)
           (== exp `(* ,e1 ,e2))
           (not-in-envo '* env)
           (multiplication-outer-ko e2 env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo e1 env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e k^ k*^ s^ v-out-ignore)
           (== exp `(call/cc ,e))
           (not-in-envo 'call/cc env)
           (call/cc-ko k* k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo e env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (cc-e v-e k^ k*^ s^ v-out-ignore)
           (== exp `(throw ,cc-e ,v-e))
           (not-in-envo 'throw env)
           (throw-ko v-e env k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo cc-e env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (cc cont body env^ s^ loc v-out-ignore)
           (== exp `(letcc ,cc ,body))
           (not-in-envo 'letcc env)
           (new-loco s loc)
           (make-continuationo k* cont)
           ;  maybe? or maybe this is just too much like call/cc and we loose any connection
           ; (== cont v-out)
           (ext-envo cc loc env env^)
           (ext-so loc cont s s^)
           (eval-exp-auxo body env^ s^ k* v/s^ v-out-ignore))]
        [(fresh (x body ans proc)
           (== exp `(lambda (,x) ,body))
           (symbolo x)
           (not-in-envo 'lambda env)
           (make-proco x body env proc)
           (== proc v-out)
           (answero proc s ans)
           (apply-k*o k* ans v/s^))]
        [(fresh (x rhs k^ k*^ s^ v-out-ignore)
           (== exp `(set! ,x ,rhs))
           (not-in-envo 'set! env)
           (symbolo x)
           (set!-ko x env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo rhs env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (rand1 rand2 k^ k*^ s^ v-out-ignore)
           (== exp `(begin ,rand1 ,rand2))
           (not-in-envo 'begin env)
           (begin-outer-ko rand2 env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo rand1 env s^ k*^ v/s^ v-out-ignore))]
        [(fresh (e*)
           (== exp `(list . ,e*))
           (not-in-envo 'list env)
           (list-auxo e* env s k* v/s^ v-out))]
        [(fresh (rator rand k^ k*^ s^ v-out-ignore)
           (== exp `(,rator ,rand))
           (application-outer-ko rand env k* v-out k^)
           (new-loco s k*^)
           (ext-so k*^ k^ s s^)
           (eval-exp-auxo rator env s^ k*^ v/s^ v-out-ignore))]))))

(define list-auxo
  (lambda (e* env s k* v* v-out*)
    (conde
      [(fresh (ans)
         (== e* '())
         (== v-out* '())
         (answero '() s ans)
         (apply-k*o k* ans v*))]
      [(fresh (a d k^ k*^ s^ v-out v-out-rest)
         (== `(,a . ,d) e*)
         (== `(,v-out . ,v-out-rest) v-out*)
         (list-aux-outer-ko e* env k* v-out-rest k^)
         (new-loco s k*^)
         (ext-so k*^ k^ s s^)
         (eval-exp-auxo a env s^ k*^ v* v-out))])))

(define eval-expo
  (lambda (exp env s k* v)
    (fresh (v/s^ s^ v-out k)
      (apply-so s k* k)
      (== v/s^ `(,v . ,s^))
      (conde
        [(== empty-k k)
         (== v v-out)
         ]
        [(=/= empty-k k)])
      (eval-exp-auxo exp env s k* v/s^ v-out))))

(define evalo
  (lambda (e o)
    (fresh (k* s)
      (new-loco empty-store k*)
      (ext-so k* empty-k empty-store s)
      (eval-expo e empty-env s k* o))))

(define cesk-tests
  (test-suite
    "tests for the cKanren cesk implementation"

    (test-case
      "supporting relation tests"

      (check-equal?
        (run #f (q)
          (fresh (loc env s)
            (new-loco empty-store loc)
            (ext-envo 'a loc empty-env env)
            (ext-so loc 7 empty-store s)
            (lookupo env s 'a q)))
        '(7)
        "lookup")

      (check-equal?
        (run #f (q)
          (fresh (addr env s)
            (new-loco empty-store addr)
            (ext-envo 'a addr empty-env env)
            (ext-so addr 'foo empty-store s)
            (lookupo env s 'a q)))
        '(foo)
        "lookup-2"))

    (test-case
      "tests for the cesk machine running forward (from scheme-version tests)"

      (check-equal?
        (run #f (q) (evalo '5 q))
        '(5)
        "cesk-number")

      (check-equal?
        (run #f (q) (evalo '#t q))
        '(#t)
        "cesk-boolean")

      (check-equal?
        (run #f (q)
          (fresh (addr env s s^ k*)
            (new-loco empty-store addr)
            (ext-envo 'a addr empty-env env)
            (ext-so addr 7 empty-store s)
            (new-loco s k*)
            (ext-so k* empty-k s s^)
            (eval-expo 'a env s^ k* q)))
        '(7)
        "cesk-variable")

      (check-equal?
        (run #f (q)
          (fresh (addr env s k* s^)
            (new-loco empty-store addr)
            (ext-envo 'a addr empty-env env)
            (ext-so addr 'foo empty-store s)
            (new-loco s k*)
            (ext-so k* empty-k s s^)
            (eval-expo 'a env s^ k* q)))
        '(foo)
        "cesk-variable-2")

      (check-equal?
        (run #f (q) (evalo '((lambda (x) x) 5) q))
        '(5)
        "cesk-identity")

      (check-equal?
        (run #f (q) (evalo '((lambda (x) x) (quote foo)) q))
        '(foo)
        "cesk-identity-2")

      (check-equal?
        (run #f (q) 
          (fresh (k* s k*^ s^ k v-out v/s^)
            (new-loco empty-store k*)
            (ext-so k* empty-k empty-store s)
            (eval-exp-auxo '(letcc k k) empty-env s k* v/s^ v-out)
            (== `((continuation ,k*^) . ,s^) v/s^)
            (apply-so s^ k*^ k)
            (== `(continuation ,k) q)))
        `((continuation ,empty-k))
        "letcc/throw-0")

      (check-equal?
        (run #f (q) (evalo '(letcc k 1) q))
        '(1)
        "letcc/throw-0b")

      (check-equal?
        (run #f (q) (evalo '(letcc k (throw k 1)) q))
        '(1)
        "letcc/throw-0c")

      (check-equal?
        (run #f (q) (evalo '(letcc k (* 5 (throw k (* 2 6)))) q))
        '(12)
        "letcc/throw-1")

      (check-equal?
        (run #f (q)
          (evalo '(letcc k
                    ((quote 5)
                      (throw k (quote 7))))
            q))
        '(7)
        "letcc/throw-2")

      (check-equal?
        (run #f (q) (evalo '((lambda (x) (begin (set! x 5) x)) 6) q))
        '(5)
        "cesk-set!")

      (check-equal?
        (run #f (q) (evalo '(quote (lambda (x) 5)) q))
        '((lambda (x) 5))
        "cesk-quote")

      (check-equal?
        (run #f (q) (evalo '(quote (lambda (x) x)) q))
        '((lambda (x) x))
        "cesk-quote-2")

      (check-equal?
        (run #f (q) (evalo '(zero? ((lambda (x) x) 0)) q))
        '(#t)
        "cesk-zero?-1")

      (check-equal?
        (run #f (q) (evalo '(zero? ((lambda (x) x) 1)) q))
        '(#f)
        "cesk-zero?-2")

      (check-equal?
        (run #f (q) (evalo '(- ((lambda (x) x) 7) ((lambda (x) x) 4)) q))
        '(3)
        "cesk-subtraction")

      (check-equal?
        (run #f (q) (evalo '(+ ((lambda (x) x) 7) ((lambda (x) x) 4)) q))
        '(11)
        "cesk-addition")

      (check-equal?
        (run #f (q) (evalo '(* ((lambda (x) x) 7) ((lambda (x) x) 4)) q))
        '(28)
        "cesk-multiplication")

      (check-equal?
        (run #f (q)
          (evalo
            '(if (zero? (- 7 4))
                 ((lambda (x) x)
                   (list (quote foo) (quote bar)))
                 ((lambda (x) x) (list #f #t)))
            q))
        '((#f #t))
        "cesk-if-1")

      (check-equal?
        (run #f (q)
          (evalo
            '(if (zero? (- 6 (* 2 3)))
                 ((lambda (x) x) (list (quote foo) (quote bar)))
                 ((lambda (x) x) (list #f #t)))
            q))
        '((foo bar))
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
        (run #f (q) (evalo fact-five q))
        '(120)
        "cesk-fact-5")

      (check-equal?
        (run #f (q) (evalo '(list) q))
        '(())
        "cesk-list-0")

      (check-equal?
        (run #f (q) (evalo '(list 5) q))
        '((5))
        "cesk-list-1")

      (check-equal?
        (run #f (q) (evalo '(list 5 6) q))
        '((5 6))
        "cesk-list-2")

      (check-equal?
        (run #f (q)
          (evalo
            '(list
               (zero? (- 6 (* 2 3)))
               ((lambda (x) x) (list (quote foo) (quote bar)))
               ((lambda (x) x) (list #f #t)))
            q))
        '((#t (foo bar) (#f #t)))
        "cesk-list-3")

      (check-equal?
        (run #f (q) (evalo '(list (quote foo)) q))
        '((foo))
        "cesk-list-1a")

      (check-equal?
        (run #f (q) (evalo '(list (quote foo) (quote bar)) q))
        '((foo bar))
        "cesk-list-2a")

      (check-equal?
        (run #f (q)
          (evalo
            '(list
               (quote baz)
               ((lambda (x) x) (list (quote foo) (quote bar)))
               ((lambda (x) x) (list (quote quux))))
            q))
        '((baz (foo bar) (quux)))
        "cesk-list-3a")

      (check-equal?
        (run #f (q) (evalo '((lambda (sub1) (sub1 3)) (lambda (n) (* n n))) q))
        '(9)
        "cesk-shadowing")

      (check-equal?
        (run #f (q)
          (evalo '((lambda (x)
                     ((lambda (quote)
                        (quote x))
                       (lambda (y) (list y y y))))
                    (quote bar))
            q))
        '((bar bar bar))
        "cesk-shadowing-2")

      (check-equal?
        (run #f (q) (evalo '(call/cc (lambda (k) 20)) q))
        '(20)
        "call/cc-1")

      (check-equal?
        (run #f (q) (evalo '(call/cc (lambda (k) (k 20))) q))
        '(20)
        "call/cc-2")

      (check-equal?
        (run #f (q) (evalo '(call/cc (lambda (k) (* 5 4))) q))
        (list (call/cc (lambda (k) (* 5 4))))
        "call/cc-3")

      (check-equal?
        (run #f (q) (evalo '(call/cc (lambda (k) (k (* 5 4)))) q))
        (list (call/cc (lambda (k) (k (* 5 4)))))
        "call/cc-4")

      (check-equal?
        (run #f (q) (evalo '(call/cc (lambda (k) (* 5 (k 4)))) q))
        (list (call/cc (lambda (k) (* 5 (k 4)))))
        "call/cc-5")

      (check-equal?
        (run #f (q) (evalo '(+ 2 (call/cc (lambda (k) (* 5 (k 4))))) q))
        (list (+ 2 (call/cc (lambda (k) (* 5 (k 4))))))
        "call/cc-6")

      (check-equal?
        (run #f (q) (evalo '(((call/cc (lambda (k) k)) (lambda (x) x)) 1) q))
        (list (((call/cc (lambda (k) k)) (lambda (x) x)) 1))
        "call/cc-7")

      (define quinec
        '((lambda (x)
            (list x (list (quote quote) x)))
           (quote
             (lambda (x)
               (list x (list (quote quote) x))))))

      (check-equal?
        (run #f (q) (evalo quinec q))
        (list quinec)
        "cesk-quinec"))

    (test-case
      "tests for the cesk machine running forward (from relational-cesk tests)"

      (check-equal?
        (run #f (q)
          (evalo
            '((lambda (make-cell)
                ((lambda (c1) ((c1 (lambda (bang) (lambda (get) get))) c1))
                  (make-cell (quote 3))))
               (lambda (value)
                 (((lambda (bang)
                     (lambda (get)
                       (lambda (f)
                         ((f bang) get))))
                    (lambda (new-value) (set! value new-value)))
                   (lambda (dummy) value))))
            q))
        '(3)
        "cell-get-1")

      (check-equal?
        (run* (q)
          (evalo
            '((lambda (make-cell)
                ((lambda (c1) (c1 (lambda (bang) (lambda (get) (get c1)))))
                  (make-cell (quote 3))))
               (lambda (value)
                 (((lambda (bang)
                     (lambda (get)
                       (lambda (f)
                         ((f bang) get))))
                    (lambda (new-value) (set! value new-value)))
                   (lambda (dummy) value))))
            q))
        '(3)
        "cell-get-2")

      (check-equal?
        (run #f (q)
          (evalo
            '((lambda (make-cell)
                ((lambda (c1)
                   (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
                  (make-cell (quote 3))))
               (lambda (value)
                 (((lambda (bang)
                     (lambda (get)
                       (lambda (f)
                         ((f bang) get))))
                    (lambda (new-value) (set! value new-value)))
                   (lambda (dummy) value))))
            q))
        '(4)
        "cell-set-1")

      ;;; mutable list
      (check-equal?
        (run #f (q)
          (evalo
            `((lambda (new-list)
                ((lambda (l)
                   (l (lambda (freeze) (lambda (set-first!) (lambda (set-second!) (freeze l))))))
                  ((new-list (quote first)) (quote second))))
               (lambda (first)
                 (lambda (second)
                   ((lambda (freeze)
                      ((lambda (set-first!)
                         ((lambda (set-second!)
                            (lambda (f)
                              (((f freeze) set-first!) set-second!)))
                           (lambda (new-second) (set! second new-second))))
                        (lambda (new-first) (set! first new-first))))
                     (lambda (dummy) (list first second))))))
            q))
        '((first second))
        "mutable-list-1")

      (check-equal?
        (run #f (q)
          (evalo
            `((lambda (new-list)
                ((lambda (l)
                   (l (lambda (freeze) (lambda (set-first!) (lambda (set-second!)
                                                              ((lambda (ignore) (freeze l))
                                                                (set-first! (quote coming))))))))
                  ((new-list (quote first)) (quote second))))
               (lambda (first)
                 (lambda (second)
                   ((lambda (freeze)
                      ((lambda (set-first!)
                         ((lambda (set-second!)
                            (lambda (f)
                              (((f freeze) set-first!) set-second!)))
                           (lambda (new-second) (set! second new-second))))
                        (lambda (new-first) (set! first new-first))))
                     (lambda (dummy) (list first second))))))
            q))
        '((coming second))
        "mutable-list-2")

      (check-equal?
        (run #f (q)
          (evalo
            `((lambda (new-list)
                ((lambda (l)
                   (l (lambda (freeze) (lambda (set-first!) (lambda (set-second!)
                                                              ((lambda (ignore) (freeze l))
                                                                ((lambda (ignore)
                                                                   (set-first! (quote hello)))
                                                                  (set-second! (quote world)))))))))
                  ((new-list (quote first)) (quote second))))
               (lambda (first)
                 (lambda (second)
                   ((lambda (freeze)
                      ((lambda (set-first!)
                         ((lambda (set-second!)
                            (lambda (f)
                              (((f freeze) set-first!) set-second!)))
                           (lambda (new-second) (set! second new-second))))
                        (lambda (new-first) (set! first new-first))))
                     (lambda (dummy) (list first second))))))
            q))
        '((hello world))
        "mutable-list-3")

      (check-equal?
        (run #f (q)
          (evalo
            `((lambda (new-list)
                ((lambda (l)
                   (l (lambda (freeze) (lambda (set-first!) (lambda (set-second!)
                                                              ((lambda (ignore) (freeze l))
                                                                ((lambda (ignore)
                                                                   (set-first! (quote coming)))
                                                                  (set-first! (quote ignored)))))))))
                  ((new-list (quote first)) (quote second))))
               (lambda (first)
                 (lambda (second)
                   ((lambda (freeze)
                      ((lambda (set-first!)
                         ((lambda (set-second!)
                            (lambda (f)
                              (((f freeze) set-first!) set-second!)))
                           (lambda (new-second) (set! second new-second))))
                        (lambda (new-first) (set! first new-first))))
                     (lambda (dummy) (list first second))))))
            q))
        '((coming second))
        "mutable-list-4")

      (check-equal?
        (run #f (q) (evalo '(quote x) q))
        '(x)
        "cesk-quote-a")

      (check-equal?
        (run #f (q) (evalo '(quote (lambda (x) x)) q))
        '((lambda (x) x))
        "cesk-quote")

      (check-equal?
        (run #f (q) (evalo '(list) q))
        '(())
        "cesk-list-0")

      (check-equal?
        (run #f (q) (evalo '(lambda (x) x) q))
        '((closure x x (() ())))
        "cesk-closure")

      (check-equal?
        (run #f (q) (evalo '((lambda (x) x) (lambda (y) y)) q))
        '((closure y y (() ())))
        "cesk-identity-a")

      (check-equal?
        (run #f (q) (evalo '((lambda (x) x) (quote foo)) q))
        '(foo)
        "cesk-identity-b")

      (check-equal?
        (run #f (q) (evalo '(list (quote foo)) q))
        '((foo))
        "cesk-list-1")

      (check-equal?
        (run #f (q) (evalo '(list (quote foo) (quote bar)) q))
        '((foo bar))
        "cesk-list-2")

      (check-equal?
        (run #f (q) (evalo '((lambda (x) (quote bar)) (list (quote foo))) q))
        '(bar)
        "cesk-list-application-1")

      (check-equal?
        (run #f (q)
          (evalo '(list (quote baz)
                    ((lambda (x) x) (list (quote foo) (quote bar)))
                    ((lambda (x) x) (list (quote quux))))
            q))
        '((baz (foo bar) (quux)))
        "cesk-list-3")

      (check-equal?
        (run #f (q)
          (evalo '((lambda (x)
                     ((lambda (quote)
                        (quote x))
                       (lambda (y) (list y y y))))
                    (quote bar))
            q))
        '((bar bar bar))
        "cesk-shadowing")

      (check-equal?
        (run #f (q)
          (evalo '(((lambda (y)
                      (lambda (x) y))
                     (quote foo))
                    (quote bar))
            q))
        '(foo)
        "cesk-nested-lambda"))

  (time
    (run 1 (q)
      (fresh (code-bang code-get code-bang-part)
        (absento 4 code-bang)
        (absento 4 code-get)
        (== code-bang `(lambda (new-value) ,code-bang-part))
        (== code-get `(lambda (dummy) value))
        (evalo
          `((lambda (make-cell)
              ((lambda (c1)
                 (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
                (make-cell (quote 3))))
             (lambda (value)
               (((lambda (bang)
                   (lambda (get)
                     (lambda (f)
                       ((f bang) get))))
                  ,code-bang)
                 ,code-get)))
          '4)
        (== q `(,code-bang ,code-get)))))

  ;; tests from the cesk-scheme-tests.scm file.
  (test-case
    "tests where some logical variables need to be filled in"
    (check-equal?
      (run 1 (q)
        (fresh (code-bang code-get code-bang-part)
          (absento 4 code-bang)
          (absento 4 code-get)
          (== code-bang `(lambda (new-value) ,code-bang-part))
          (== code-get `(lambda (dummy) value))
          (evalo
            `((lambda (make-cell)
                ((lambda (c1)
                   (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
                  (make-cell (quote 3))))
               (lambda (value)
                 (((lambda (bang)
                     (lambda (get)
                       (lambda (f)
                         ((f bang) get))))
                    ,code-bang)
                   ,code-get)))
            '4)
          (== q `(,code-bang ,code-get))))
      '(((lambda (new-value) (set! value new-value))
          (lambda (dummy) value)))
      "cell-guess-paper-1"))

  (check-equal?
        (run #f (q)
          (evalo
            '((lambda (make-cell)
                ((lambda (c1)
                   (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
                  (make-cell (quote 3))))
               (lambda (value)
                 (((lambda (bang)
                     (lambda (get)
                       (lambda (f)
                         ((f bang) get))))
                    (lambda (new-value) (set! value new-value)))
                   (lambda (dummy) value))))
            q))
        '(4)
        "cell-set-1")
#|
  (test-case
    "tests where some logical variables need to be filled in"
    (check-equal?
      (run 1 (q)
        (fresh (code-bang code-bang-part)
          (absento 4 code-bang)
          (== code-bang `(lambda (new-value) ,code-bang-part))
          (evalo
            `((lambda (make-cell)
                ((lambda (c1)
                   (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
                  (make-cell (quote 3))))
               (lambda (value)
                 (((lambda (bang)
                     (lambda (get)
                       (lambda (f)
                         ((f bang) get))))
                    ,code-bang)
                   (lambda (dummy) value))))
            '4)
          (== q code-bang)))
      '((lambda (new-value) (set! value new-value)))
      "cell-guess-paper-1"))

  (run 1 (q)
    (fresh (code-bang code-bang-part)
      (absento 4 code-bang)
      (== code-bang `(lambda (new-value) (set! value new-value)))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               (lambda (dummy) value))))
        '4)
      (== q code-bang)))

  (time
  (run 1 (q)
    (fresh (code-bang code-bang-part ans)
      (absento 4 code-bang)
      (== code-bang `(lambda (new-value) ,code-bang-part))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               (lambda (dummy) value))))
        ans)
      (== q `(,code-bang ,ans))
      (== code-bang-part `(set! value new-value)))))
|#

#|
  (test "cell-guess-1"
    (run 1 (q)
      (fresh (code-bang code-get)
        (absento 4 code-bang)
        (absento 4 code-get)
        (== code-bang '(lambda (new-value) (set! value new-value)))
        (== code-get '(lambda (dummy) value))
        (evalo
          `((lambda (make-cell)
              ((lambda (c1)
                 (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
                (make-cell (quote 3))))
             (lambda (value)
               (((lambda (bang)
                   (lambda (get)
                     (lambda (f)
                       ((f bang) get))))
                  ,code-bang)
                 ,code-get)))
          '4)
        (== q `(,code-bang ,code-get))))
    '(((lambda (new-value) (set! value new-value))
        (lambda (dummy) value))))

(test "cell-guess-2"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang `(lambda (new-value) (set! value ,code-bang-part)))
      (== code-get '(lambda (dummy) value))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

(test "cell-guess-3"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part code-get-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang `(lambda (new-value) (set! value ,code-bang-part)))
      (== code-get `(lambda (dummy) ,code-get-part))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

(test "cell-guess-4"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (absento 'throw code-bang)
      (== code-bang `(lambda (new-value) ,code-bang-part))
      (== code-get `(lambda (dummy) value))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

(test "cell-guess-5"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part code-get-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang `(lambda (new-value) (set! . ,code-bang-part)))
      (== code-get `(lambda (dummy) ,code-get-part))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
      (lambda (dummy) value))))
|#

#|
  (test "combined-list-test-1"
    (length
      (run 50 (q)
        (fresh (expr env store k val)
          (== '(list (quote foo)) expr)
          (== empty-env env)
          (== empty-store store)
          (== `(,expr ,env ,store ,k ,val) q)
          (eval-expo-simple
            expr
            env
            store
            k
            val)
          (condu
            [(eval-expo expr env store k val)]
            [(errorg 'combined-test-1 "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
    50)

(test "combined-test-1"
  (length
   (run 50 (q)
    (fresh (expr env store k val)
      (== `(,expr ,env ,store ,k ,val) q)
      (eval-expo-simple
       expr
       env
       store
       k
       val)
      (condu
        [(eval-expo expr env store k val)]
        [(errorg 'combined-test-1 "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
  50)

(test "combined-test-2"
  (length
   (run 50 (q)
    (fresh (expr env store k val)
      (== `(,expr ,env ,store ,k ,val) q)
      (eval-expo
       expr
       env
       store
       k
       val)
      (condu
        [(eval-expo-simple expr env store k val)]
        [(errorg 'combined-test-2 "eval-expo-simple can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
  50)

(test "cesk-list-1-backwards"
  (run 3 (q)
    (evalo q '(foo)))
  '('(foo)
    (list 'foo)
    (((lambda (_.0) '(foo)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))))

(test "cesk-list-2-backwards"
  (run 3 (q)
    (fresh (x body)
      (evalo `(lambda (,x) ,body) '(foo))))
  '())

(test "cesk-list-2b"
  (run 5 (q)
    (evalo q '(foo bar)))
  '('(foo bar)
    (list 'foo 'bar)
    (((lambda (_.0) '(foo bar)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((lambda (_.0) _.0) '(foo bar)) (sym _.0))
    (((lambda (_.0) '(foo bar)) (lambda (_.1) _.2))
     (=/= ((_.0 quote)))
     (sym _.0 _.1))))
|#

#|
(test "cesk-set!-0"
  (run 20 (q)
    (fresh (expr env store k val)
      (eval-expo
       expr
       env
       store
       k
       val)
       (fails-unless-contains env 'set!)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (empty-k) void) (=/= ((_.0 quote)) ((_.0 set!))) (num _.3) (sym _.0) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.0 . _.3) (_.4 _.5 . _.6)) (_.7 _.8) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!))) (num _.4 _.5) (sym _.0 _.2) (absento (closure _.1) '_.3 (set! _.3) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.0 . _.3) (_.4 . _.5)) (_.6 _.7) (empty-k) void) (=/= ((_.0 lambda)) ((_.0 set!))) (num _.4) (sym _.0 _.1) (absento (lambda _.3) (set! _.3)))
     (((set! _.0 '_.1) ((_.2 _.3 _.0 . _.4) (_.5 _.6 _.7 . _.8)) (_.9 _.10) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!))) (num _.5 _.6 _.7) (sym _.0 _.2 _.3) (absento (closure _.1) '_.4 (set! _.4) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.0 . _.5) (_.6 _.7 _.8 _.9 . _.10)) (_.11 _.12) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!))) (num _.6 _.7 _.8 _.9) (sym _.0 _.2 _.3 _.4) (absento (closure _.1) '_.5 (set! _.5) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.0 . _.4) (_.5 _.6 . _.7)) (_.8 _.9) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!))) (num _.5 _.6) (sym _.0 _.1 _.3) (absento (lambda _.4) (set! _.4)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.0 . _.6) (_.7 _.8 _.9 _.10 _.11 . _.12)) (_.13 _.14) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!))) (num _.10 _.11 _.7 _.8 _.9) (sym _.0 _.2 _.3 _.4 _.5) (absento (closure _.1) '_.6 (set! _.6) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.0 . _.7) (_.8 _.9 _.10 _.11 _.12 _.13 . _.14)) (_.15 _.16) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!))) (num _.10 _.11 _.12 _.13 _.8 _.9) (sym _.0 _.2 _.3 _.4 _.5 _.6) (absento (closure _.1) '_.7 (set! _.7) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.0 . _.5) (_.6 _.7 _.8 . _.9)) (_.10 _.11) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!))) (num _.6 _.7 _.8) (sym _.0 _.1 _.3 _.4) (absento (lambda _.5) (set! _.5)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.0 . _.8) (_.9 _.10 _.11 _.12 _.13 _.14 _.15 . _.16)) (_.17 _.18) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!))) (num _.10 _.11 _.12 _.13 _.14 _.15 _.9) (sym _.0 _.2 _.3 _.4 _.5 _.6 _.7) (absento (closure _.1) '_.8 (set! _.8) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.0 . _.9) (_.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 . _.18)) (_.19 _.20) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!))) (num _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17) (sym _.0 _.2 _.3 _.4 _.5 _.6 _.7 _.8) (absento (closure _.1) '_.9 (set! _.9) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.0 . _.6) (_.7 _.8 _.9 _.10 . _.11)) (_.12 _.13) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!))) (num _.10 _.7 _.8 _.9) (sym _.0 _.1 _.3 _.4 _.5) (absento (lambda _.6) (set! _.6)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.0 . _.10) (_.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 . _.20)) (_.21 _.22) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19) (sym _.0 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.10 (set! _.10) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.0 . _.11) (_.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 . _.22)) (_.23 _.24) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21) (sym _.0 _.10 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.11 (set! _.11) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.0 . _.7) (_.8 _.9 _.10 _.11 _.12 . _.13)) (_.14 _.15) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!))) (num _.10 _.11 _.12 _.8 _.9) (sym _.0 _.1 _.3 _.4 _.5 _.6) (absento (lambda _.7) (set! _.7)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.0 . _.12) (_.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 . _.24)) (_.25 _.26) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23) (sym _.0 _.10 _.11 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.12 (set! _.12) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.0 . _.13) (_.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 . _.26)) (_.27 _.28) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25) (sym _.0 _.10 _.11 _.12 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.13 (set! _.13) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.0 . _.8) (_.9 _.10 _.11 _.12 _.13 _.14 . _.15)) (_.16 _.17) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!))) (num _.10 _.11 _.12 _.13 _.14 _.9) (sym _.0 _.1 _.3 _.4 _.5 _.6 _.7) (absento (lambda _.8) (set! _.8)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.0 . _.14) (_.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 . _.28)) (_.29 _.30) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27) (sym _.0 _.10 _.11 _.12 _.13 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.14 (set! _.14) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.0 . _.15) (_.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 . _.30)) (_.31 _.32) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.15 (set! _.15) (void _.1)))))

 (test "cesk-set!-1"
   (run 50 (q)
     (fresh (expr env store k val x e)
       (== `(set! ,x ,e) expr)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (empty-k) void) (=/= ((_.0 quote)) ((_.0 set!))) (num _.3) (sym _.0) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.0 . _.3) (_.4 _.5 . _.6)) (_.7 _.8) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!))) (num _.4 _.5) (sym _.0 _.2) (absento (closure _.1) '_.3 (set! _.3) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.0 . _.3) (_.4 . _.5)) (_.6 _.7) (empty-k) void) (=/= ((_.0 lambda)) ((_.0 set!))) (num _.4) (sym _.0 _.1) (absento (lambda _.3) (set! _.3)))
     (((set! _.0 '_.1) ((_.2 _.3 _.0 . _.4) (_.5 _.6 _.7 . _.8)) (_.9 _.10) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!))) (num _.5 _.6 _.7) (sym _.0 _.2 _.3) (absento (closure _.1) '_.4 (set! _.4) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.0 . _.5) (_.6 _.7 _.8 _.9 . _.10)) (_.11 _.12) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!))) (num _.6 _.7 _.8 _.9) (sym _.0 _.2 _.3 _.4) (absento (closure _.1) '_.5 (set! _.5) (void _.1)))
     (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (set!-k _.7 ((_.7 . _.8) (_.9 . _.10)) (empty-k)) void) (=/= ((_.0 quote)) ((_.0 set!))) (num _.3 _.9) (sym _.0 _.7) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.0 . _.4) (_.5 _.6 . _.7)) (_.8 _.9) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!))) (num _.5 _.6) (sym _.0 _.1 _.3) (absento (lambda _.4) (set! _.4)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.0 . _.6) (_.7 _.8 _.9 _.10 _.11 . _.12)) (_.13 _.14) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!))) (num _.10 _.11 _.7 _.8 _.9) (sym _.0 _.2 _.3 _.4 _.5) (absento (closure _.1) '_.6 (set! _.6) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.0 . _.7) (_.8 _.9 _.10 _.11 _.12 _.13 . _.14)) (_.15 _.16) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!))) (num _.10 _.11 _.12 _.13 _.8 _.9) (sym _.0 _.2 _.3 _.4 _.5 _.6) (absento (closure _.1) '_.7 (set! _.7) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.0 . _.5) (_.6 _.7 _.8 . _.9)) (_.10 _.11) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!))) (num _.6 _.7 _.8) (sym _.0 _.1 _.3 _.4) (absento (lambda _.5) (set! _.5)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.0 . _.8) (_.9 _.10 _.11 _.12 _.13 _.14 _.15 . _.16)) (_.17 _.18) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!))) (num _.10 _.11 _.12 _.13 _.14 _.15 _.9) (sym _.0 _.2 _.3 _.4 _.5 _.6 _.7) (absento (closure _.1) '_.8 (set! _.8) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.0 . _.9) (_.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 . _.18)) (_.19 _.20) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!))) (num _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17) (sym _.0 _.2 _.3 _.4 _.5 _.6 _.7 _.8) (absento (closure _.1) '_.9 (set! _.9) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.0 . _.6) (_.7 _.8 _.9 _.10 . _.11)) (_.12 _.13) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!))) (num _.10 _.7 _.8 _.9) (sym _.0 _.1 _.3 _.4 _.5) (absento (lambda _.6) (set! _.6)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.0 . _.10) (_.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 . _.20)) (_.21 _.22) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19) (sym _.0 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.10 (set! _.10) (void _.1)))
     (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (set!-k _.7 ((_.8 _.7 . _.9) (_.10 _.11 . _.12)) (empty-k)) void) (=/= ((_.0 quote)) ((_.0 set!)) ((_.7 _.8))) (num _.10 _.11 _.3) (sym _.0 _.7 _.8) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (list-aux-inner-k _.7 (empty-k)) (_.7 . void)) (=/= ((_.0 quote)) ((_.0 set!))) (num _.3) (sym _.0) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.0 . _.3) (_.4 _.5 . _.6)) (_.7 _.8) (set!-k _.9 ((_.9 . _.10) (_.11 . _.12)) (empty-k)) void) (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!))) (num _.11 _.4 _.5) (sym _.0 _.2 _.9) (absento (closure _.1) '_.3 (set! _.3) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.0 . _.11) (_.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 . _.22)) (_.23 _.24) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21) (sym _.0 _.10 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.11 (set! _.11) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.0 . _.3) (_.4 . _.5)) (_.6 _.7) (set!-k _.8 ((_.8 . _.9) (_.10 . _.11)) (empty-k)) void) (=/= ((_.0 lambda)) ((_.0 set!))) (num _.10 _.4) (sym _.0 _.1 _.8) (absento (lambda _.3) (set! _.3)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.0 . _.7) (_.8 _.9 _.10 _.11 _.12 . _.13)) (_.14 _.15) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!))) (num _.10 _.11 _.12 _.8 _.9) (sym _.0 _.1 _.3 _.4 _.5 _.6) (absento (lambda _.7) (set! _.7)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.0 . _.12) (_.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 . _.24)) (_.25 _.26) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23) (sym _.0 _.10 _.11 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.12 (set! _.12) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.0 . _.13) (_.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 . _.26)) (_.27 _.28) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25) (sym _.0 _.10 _.11 _.12 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.13 (set! _.13) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.0 . _.8) (_.9 _.10 _.11 _.12 _.13 _.14 . _.15)) (_.16 _.17) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!))) (num _.10 _.11 _.12 _.13 _.14 _.9) (sym _.0 _.1 _.3 _.4 _.5 _.6 _.7) (absento (lambda _.8) (set! _.8)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.0 . _.14) (_.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 . _.28)) (_.29 _.30) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27) (sym _.0 _.10 _.11 _.12 _.13 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.14 (set! _.14) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.0 . _.15) (_.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 . _.30)) (_.31 _.32) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.15 (set! _.15) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.8 _.0 . _.9) (_.10 _.11 _.12 _.13 _.14 _.15 _.16 . _.17)) (_.18 _.19) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!)) ((_.8 lambda)) ((_.8 set!))) (num _.10 _.11 _.12 _.13 _.14 _.15 _.16) (sym _.0 _.1 _.3 _.4 _.5 _.6 _.7 _.8) (absento (lambda _.9) (set! _.9)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.0 . _.16) (_.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 . _.32)) (_.33 _.34) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.16 (set! _.16) (void _.1)))
     (((set! _.0 _.0) ((_.0 . _.1) (_.2 . _.3)) ((_.2 . _.4) (_.5 . _.6)) (empty-k) void) (=/= ((_.0 set!))) (num _.2) (sym _.0) (absento (set! _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.0 . _.17) (_.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 . _.34)) (_.35 _.36) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.17 (set! _.17) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.8 _.9 _.0 . _.10) (_.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 . _.19)) (_.20 _.21) (empty-k) void) (=/= ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!)) ((_.8 lambda)) ((_.8 set!)) ((_.9 lambda)) ((_.9 set!))) (num _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18) (sym _.0 _.1 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (lambda _.10) (set! _.10)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.0 . _.18) (_.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 . _.36)) (_.37 _.38) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.18 (set! _.18) (void _.1)))
     (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (application-inner-k (closure _.7 '_.8 (_.9 _.10)) (empty-k) _.8) _.8) (=/= ((_.0 quote)) ((_.0 set!)) ((_.7 quote))) (num _.3) (sym _.0 _.7) (absento (closure _.1) (closure _.8) '_.2 '_.9 (set! _.2) (void _.1) (void _.8)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.0 . _.19) (_.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 . _.38)) (_.39 _.40) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.18)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.18 quote)) ((_.18 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.19 (set! _.19) (void _.1)))
     (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (set!-k _.7 ((_.8 _.9 _.7 . _.10) (_.11 _.12 _.13 . _.14)) (empty-k)) void) (=/= ((_.0 quote)) ((_.0 set!)) ((_.7 _.8)) ((_.7 _.9))) (num _.11 _.12 _.13 _.3) (sym _.0 _.7 _.8 _.9) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.0 . _.3) (_.4 _.5 . _.6)) (_.7 _.8) (set!-k _.9 ((_.10 _.9 . _.11) (_.12 _.13 . _.14)) (empty-k)) void) (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.10 _.9)) ((_.2 quote)) ((_.2 set!))) (num _.12 _.13 _.4 _.5) (sym _.0 _.10 _.2 _.9) (absento (closure _.1) '_.3 (set! _.3) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.0 . _.11) (_.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 . _.21)) (_.22 _.23) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 lambda)) ((_.0 set!)) ((_.10 lambda)) ((_.10 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!)) ((_.8 lambda)) ((_.8 set!)) ((_.9 lambda)) ((_.9 set!))) (num _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20) (sym _.0 _.1 _.10 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (lambda _.11) (set! _.11)))
     (((set! _.0 '_.1) ((_.2 _.0 . _.3) (_.4 _.5 . _.6)) (_.7 _.8) (list-aux-inner-k _.9 (empty-k)) (_.9 . void)) (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!))) (num _.4 _.5) (sym _.0 _.2) (absento (closure _.1) '_.3 (set! _.3) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.0 . _.20) (_.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 . _.40)) (_.41 _.42) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.18)) ((_.0 _.19)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.18 quote)) ((_.18 set!)) ((_.19 quote)) ((_.19 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.20 (set! _.20) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.0 . _.3) (_.4 . _.5)) (_.6 _.7) (set!-k _.8 ((_.9 _.8 . _.10) (_.11 _.12 . _.13)) (empty-k)) void) (=/= ((_.0 lambda)) ((_.0 set!)) ((_.8 _.9))) (num _.11 _.12 _.4) (sym _.0 _.1 _.8 _.9) (absento (lambda _.3) (set! _.3)))
     (((set! _.0 '_.1) ((_.2 _.3 _.0 . _.4) (_.5 _.6 _.7 . _.8)) (_.9 _.10) (set!-k _.11 ((_.11 . _.12) (_.13 . _.14)) (empty-k)) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!))) (num _.13 _.5 _.6 _.7) (sym _.0 _.11 _.2 _.3) (absento (closure _.1) '_.4 (set! _.4) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.0 . _.3) (_.4 . _.5)) (_.6 _.7) (list-aux-inner-k _.8 (empty-k)) (_.8 . void)) (=/= ((_.0 lambda)) ((_.0 set!))) (num _.4) (sym _.0 _.1) (absento (lambda _.3) (set! _.3)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.0 . _.21) (_.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 . _.42)) (_.43 _.44) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.18)) ((_.0 _.19)) ((_.0 _.2)) ((_.0 _.20)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.18 quote)) ((_.18 set!)) ((_.19 quote)) ((_.19 set!)) ((_.2 quote)) ((_.2 set!)) ((_.20 quote)) ((_.20 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.2 _.20 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.21 (set! _.21) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.0 . _.4) (_.5 _.6 . _.7)) (_.8 _.9) (set!-k _.10 ((_.10 . _.11) (_.12 . _.13)) (empty-k)) void) (=/= ((_.0 _.3)) ((_.0 lambda)) ((_.0 set!)) ((_.3 lambda)) ((_.3 set!))) (num _.12 _.5 _.6) (sym _.0 _.1 _.10 _.3) (absento (lambda _.4) (set! _.4)))
     (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (set!-k _.7 ((_.7 . _.8) (_.9 . _.10)) (set!-k _.11 ((_.11 . _.12) (_.13 . _.14)) (empty-k))) void) (=/= ((_.0 quote)) ((_.0 set!))) (num _.13 _.3 _.9) (sym _.0 _.11 _.7) (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.0 . _.12) (_.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 . _.23)) (_.24 _.25) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 lambda)) ((_.0 set!)) ((_.10 lambda)) ((_.10 set!)) ((_.11 lambda)) ((_.11 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!)) ((_.8 lambda)) ((_.8 set!)) ((_.9 lambda)) ((_.9 set!))) (num _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22) (sym _.0 _.1 _.10 _.11 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (lambda _.12) (set! _.12)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.0 . _.22) (_.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 _.42 _.43 . _.44)) (_.45 _.46) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.18)) ((_.0 _.19)) ((_.0 _.2)) ((_.0 _.20)) ((_.0 _.21)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.18 quote)) ((_.18 set!)) ((_.19 quote)) ((_.19 set!)) ((_.2 quote)) ((_.2 set!)) ((_.20 quote)) ((_.20 set!)) ((_.21 quote)) ((_.21 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.23 _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 _.42 _.43) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.2 _.20 _.21 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.22 (set! _.22) (void _.1)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.0 . _.23) (_.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 _.42 _.43 _.44 _.45 . _.46)) (_.47 _.48) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.18)) ((_.0 _.19)) ((_.0 _.2)) ((_.0 _.20)) ((_.0 _.21)) ((_.0 _.22)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.18 quote)) ((_.18 set!)) ((_.19 quote)) ((_.19 set!)) ((_.2 quote)) ((_.2 set!)) ((_.20 quote)) ((_.20 set!)) ((_.21 quote)) ((_.21 set!)) ((_.22 quote)) ((_.22 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.24 _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 _.42 _.43 _.44 _.45) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.2 _.20 _.21 _.22 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.23 (set! _.23) (void _.1)))
     (((set! _.0 (lambda (_.1) _.2)) ((_.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.0 . _.13) (_.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 . _.25)) (_.26 _.27) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 lambda)) ((_.0 set!)) ((_.10 lambda)) ((_.10 set!)) ((_.11 lambda)) ((_.11 set!)) ((_.12 lambda)) ((_.12 set!)) ((_.3 lambda)) ((_.3 set!)) ((_.4 lambda)) ((_.4 set!)) ((_.5 lambda)) ((_.5 set!)) ((_.6 lambda)) ((_.6 set!)) ((_.7 lambda)) ((_.7 set!)) ((_.8 lambda)) ((_.8 set!)) ((_.9 lambda)) ((_.9 set!))) (num _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24) (sym _.0 _.1 _.10 _.11 _.12 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (lambda _.13) (set! _.13)))
     (((set! _.0 '_.1) ((_.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.0 . _.24) (_.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 _.42 _.43 _.44 _.45 _.46 _.47 . _.48)) (_.49 _.50) (empty-k) void) (=/= ((_.0 _.10)) ((_.0 _.11)) ((_.0 _.12)) ((_.0 _.13)) ((_.0 _.14)) ((_.0 _.15)) ((_.0 _.16)) ((_.0 _.17)) ((_.0 _.18)) ((_.0 _.19)) ((_.0 _.2)) ((_.0 _.20)) ((_.0 _.21)) ((_.0 _.22)) ((_.0 _.23)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8)) ((_.0 _.9)) ((_.0 quote)) ((_.0 set!)) ((_.10 quote)) ((_.10 set!)) ((_.11 quote)) ((_.11 set!)) ((_.12 quote)) ((_.12 set!)) ((_.13 quote)) ((_.13 set!)) ((_.14 quote)) ((_.14 set!)) ((_.15 quote)) ((_.15 set!)) ((_.16 quote)) ((_.16 set!)) ((_.17 quote)) ((_.17 set!)) ((_.18 quote)) ((_.18 set!)) ((_.19 quote)) ((_.19 set!)) ((_.2 quote)) ((_.2 set!)) ((_.20 quote)) ((_.20 set!)) ((_.21 quote)) ((_.21 set!)) ((_.22 quote)) ((_.22 set!)) ((_.23 quote)) ((_.23 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!)) ((_.5 quote)) ((_.5 set!)) ((_.6 quote)) ((_.6 set!)) ((_.7 quote)) ((_.7 set!)) ((_.8 quote)) ((_.8 set!)) ((_.9 quote)) ((_.9 set!))) (num _.25 _.26 _.27 _.28 _.29 _.30 _.31 _.32 _.33 _.34 _.35 _.36 _.37 _.38 _.39 _.40 _.41 _.42 _.43 _.44 _.45 _.46 _.47) (sym _.0 _.10 _.11 _.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 _.2 _.20 _.21 _.22 _.23 _.3 _.4 _.5 _.6 _.7 _.8 _.9) (absento (closure _.1) '_.24 (set! _.24) (void _.1)))
     (((set! _.0 _.1) ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.3 . _.6) (_.7 . _.8)) (empty-k) void) (=/= ((_.0 _.1)) ((_.0 set!)) ((_.1 set!))) (num _.3 _.4) (sym _.0 _.1) (absento (set! _.2)))))

 (test "cesk-set!-1b"
   (length
    (run 50 (q)
     (fresh (expr env store k val x e)
       (== `(set! ,x ,e) expr)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo-simple
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo expr env store k val)]
         [(errorg 'cesk-set!-1b "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
   50)

 (test "cesk-set!-1c"
   (length
    (run 30 (q)
      (fresh (expr env store k val x e)
        (== `(set! ,x ,e) expr)
        (== `(,expr ,env ,store ,k ,val) q)
        (== `(,expr ,env ,store ,k ,val) q)
        (eval-expo
         expr
         env
         store
         k
         val)
        (condu
          [(eval-expo-simple expr env store k val)]
          [(errorg 'cesk-set!-1c "eval-expo-simpl can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
   30)

 ;;; tests related to v-out
 (test "cesk-application-inner-k-1"
   (run 5 (q)
     (fresh (expr env store k val v-out datum env^ x datum^)
       (== `(quote ,datum) expr)
       (==
        `(application-inner-k
          (closure ,x (quote ,datum^) ,env^)
          (empty-k)
          ,v-out)
        k)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((('_.0 (_.1 _.2) (_.3 _.4) (application-inner-k (closure _.5 '_.6 (_.7 _.8)) (empty-k) _.6) _.6) (=/= ((_.5 quote))) (sym _.5) (absento (closure _.0) (closure _.6) '_.1 '_.7 (void _.0) (void _.6)))
     (('_.0 (_.1 _.2) ((_.3 . _.4) ((closure _.5 '_.6 (_.7 _.8)) . _.9)) (application-inner-k (closure _.10 '(lambda (_.11) _.12) ((quote . _.13) (_.3 . _.14))) (empty-k) _.6) _.6) (=/= ((_.10 lambda)) ((_.10 quote)) ((_.5 quote))) (num _.3) (sym _.10 _.11 _.5) (absento (closure _.0) (closure _.6) (lambda _.13) '_.1 '_.7 (void _.0) (void _.6)))
     (('_.0 (_.1 _.2) ((_.3 . _.4) ((closure _.5 (lambda (_.6) _.7) (_.8 _.9)) . _.10)) (application-inner-k (closure _.11 '(lambda (_.12) _.13) ((quote . _.14) (_.3 . _.15))) (empty-k) (closure _.6 _.7 ((_.5 . _.8) (_.16 . _.9)))) (closure _.6 _.7 ((_.5 . _.8) (_.16 . _.9)))) (=/= ((_.11 lambda)) ((_.11 quote)) ((_.16 _.3)) ((_.5 lambda))) (num _.16 _.3) (sym _.11 _.12 _.5 _.6) (absento (_.16 _.4) (closure _.0) (lambda _.14) (lambda _.8) '_.1  (void _.0)))
     (('(lambda (_.0) _.1) ((quote . _.2) (_.3 . _.4)) ((_.3 . _.5) ((closure _.6 '_.7 (_.8 _.9)) . _.10)) (application-inner-k (closure _.11 '_.12 (_.13 _.14)) (empty-k) _.12) _.12) (=/= ((_.11 quote)) ((_.6 quote))) (num _.3) (sym _.0 _.11 _.6) (absento (closure _.12) (closure _.7) (lambda _.2) '_.13 '_.8  (void _.12) (void _.7)))
     (('_.0 (_.1 _.2) ((_.3 . _.4) ((closure _.5 _.5 (_.6 _.7)) . _.8)) (application-inner-k (closure _.9 '(lambda (_.10) _.11) ((quote . _.12) (_.3 . _.13))) (empty-k) (closure _.10 _.11 ((_.9 quote . _.12) (_.14 _.3 . _.13)))) (closure _.10 _.11 ((_.9 quote . _.12) (_.14 _.3 . _.13)))) (=/= ((_.14 _.3)) ((_.9 lambda)) ((_.9 quote))) (num _.14 _.3) (sym _.10 _.5 _.9) (absento (_.14 _.4) (closure _.0) (lambda _.12) '_.1 (void _.0)))))

 (test "cesk-application-inner-k-1b"
   (length
    (run 10 (q)
     (fresh (expr env store k val datum x datum^ env^ v-out)
       (== `(quote ,datum) expr)
       (==
        `(application-inner-k
          (closure ,x (quote ,datum^) ,env^)
          (empty-k)
          ,v-out)
        k)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo-simple
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo expr env store k val)]
         [(errorg 'cesk-application-inner-k-1b "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-application-inner-k-1c"
   (length
    (run 10 (q)
     (fresh (expr env store k val datum x datum^ env^ v-out)
       (== `(quote ,datum) expr)
       (==
        `(application-inner-k
          (closure ,x (quote ,datum^) ,env^)
          (empty-k)
          ,v-out)
        k)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo-simple expr env store k val)]
         [(errorg 'cesk-application-inner-k-1c "eval-expo-simpl can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-application-inner-k-2"
   (run 4 (q)
     (fresh (expr k datum x y env^ env store val v-out)
       (== `(quote ,datum) expr)
       (symbolo y)
       (==
        `(application-inner-k
          (closure ,x ,y ,env^)
          (empty-k)
          ,v-out)
        k)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((('_.0 (_.1 _.2) (_.3 _.4) (application-inner-k (closure _.5 _.5 (_.6 _.7)) (empty-k) _.0) _.0) (sym _.5) (absento (closure _.0) '_.1 (void _.0)))
     (('_.0 (_.1 _.2) ((_.3 . _.4) (_.5 . _.6)) (application-inner-k (closure _.7 _.8 ((_.8 . _.9) (_.10 . _.11))) (empty-k) _.0) _.0) (=/= ((_.10 _.3)) ((_.7 _.8))) (num _.10 _.3) (sym _.7 _.8) (absento (_.10 _.4) (closure _.0) '_.1 (void _.0)))
     (('_.0 (_.1 _.2) ((_.3 . _.4) (_.5 . _.6)) (application-inner-k (closure _.7 _.8 ((_.8 . _.9) (_.3 . _.10))) (empty-k) _.5) _.5) (=/= ((_.7 _.8))) (num _.3) (sym _.7 _.8) (absento (closure _.0) '_.1 (void _.0)))
     (('_.0 (_.1 _.2) ((_.3 _.4 . _.5) (_.6 _.7 . _.8)) (application-inner-k (closure _.9 _.10 ((_.11 _.10 . _.12) (_.13 _.14 . _.15))) (empty-k) _.0) _.0) (=/= ((_.10 _.11)) ((_.10 _.9)) ((_.14 _.3)) ((_.14 _.4))) (num _.13 _.14 _.3 _.4) (sym _.10 _.11 _.9) (absento (_.14 _.5) (closure _.0) '_.1 (void _.0)))))

 (test "cesk-application-inner-k-2b"
   (length
    (run 10 (q)
     (fresh (expr env store k val datum x y env^ v-out)
       (== `(quote ,datum) expr)
       (symbolo y)
       (==
        `(application-inner-k
          (closure ,x ,y ,env^)
          (empty-k)
          ,v-out)
        k)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo-simple
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo expr env store k val)]
         [(errorg 'cesk-application-inner-k-2b "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-application-inner-k-2c"
   (length
    (run 10 (q)
     (fresh (expr env store k val datum x y env^ v-out)
       (== `(quote ,datum) expr)
       (symbolo y)
       (==
        `(application-inner-k
          (closure ,x ,y ,env^)
          (empty-k)
          ,v-out)
        k)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo-simple expr env store k val)]
         [(errorg 'cesk-application-inner-k-2c "eval-expo-simple can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-empty-list-backwards"
   (run 8 (q)
     (fresh (expr k datum x y env^ env store val v-out)
       (== '(list) expr)
       (=/= empty-k k)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.4 . _.5) (_.6 . _.7)) (empty-k)) void) (num _.6) (sym _.4) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.4 . _.6) (_.7 _.8 . _.9)) (empty-k)) void) (=/= ((_.4 _.5))) (num _.7 _.8) (sym _.4 _.5) (absento (list _.0)))
     (((list) (_.0 _.1) _.2 (list-aux-inner-k _.3 (empty-k)) (_.3)) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 '_.5 (_.6 _.7)) (empty-k) _.5) _.5) (=/= ((_.4 quote))) (sym _.4) (absento (closure _.5) (list _.0) '_.6 (void _.5)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.6 _.4 . _.7) (_.8 _.9 _.10 . _.11)) (empty-k)) void) (=/= ((_.4 _.5)) ((_.4 _.6))) (num _.10 _.8 _.9) (sym _.4 _.5 _.6) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.4 . _.5) (_.6 . _.7)) (set!-k _.8 ((_.8 . _.9) (_.10 . _.11)) (empty-k))) void) (num _.10 _.6) (sym _.4 _.8) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 (lambda (_.5) _.6) (_.7 _.8)) (empty-k) (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8)))) (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8)))) (=/= ((_.4 lambda))) (num _.9) (sym _.4 _.5) (absento (_.9 _.2) (lambda _.7) (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.6 _.7 _.4 . _.8) (_.9 _.10 _.11 _.12 . _.13)) (empty-k)) void) (=/= ((_.4 _.5)) ((_.4 _.6)) ((_.4 _.7))) (num _.10 _.11 _.12 _.9) (sym _.4 _.5 _.6 _.7) (absento (list _.0)))))

 (test "cesk-empty-list-backwards-b"
   (length
    (run 10 (q)
     (fresh (expr env store k val)
       (== '(list) expr)
       (=/= empty-k k)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo-simple
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo expr env store k val)]
         [(errorg 'cesk-empty-list-backwards-b "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-empty-list-backwards-c"
   (length
    (run 10 (q)
     (fresh (expr env store k val)
       (== '(list) expr)
       (=/= empty-k k)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo-simple expr env store k val)]
         [(errorg 'cesk-empty-list-backwards-c "eval-expo-simple can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-empty-list-application"
   (run 4 (q)
     (fresh (expr k env store val)
       (== '((lambda (x) (quote (foo bar))) (list)) expr)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '(((((lambda (x) '(foo bar)) (list)) (_.0 _.1) (_.2 _.3) (empty-k) (foo bar)) (absento (lambda _.0) (list _.0) '_.0))
     ((((lambda (x) '(foo bar)) (list)) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.4 . _.5) (_.6 . _.7)) (empty-k)) void) (num _.6) (sym _.4) (absento (lambda _.0) (list _.0) '_.0))
     ((((lambda (x) '(foo bar)) (list)) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.4 . _.6) (_.7 _.8 . _.9)) (empty-k)) void) (=/= ((_.4 _.5))) (num _.7 _.8) (sym _.4 _.5) (absento (lambda _.0) (list _.0) '_.0))
     ((((lambda (x) '(foo bar)) (list)) (_.0 _.1) (_.2 _.3) (list-aux-inner-k _.4 (empty-k)) (_.4 foo bar)) (absento (lambda _.0) (list _.0) '_.0))))

 (test "cesk-empty-list-application-b"
   (length
    (run 10 (q)
     (fresh (expr env store k val)
       (== '((lambda (x) (quote (foo bar))) (list)) expr)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo-simple
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo expr env store k val)]
         [(errorg 'cesk-empty-list-application-b "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-empty-list-application-c"
   (length
    (run 10 (q)
     (fresh (expr env store k val)
       (== '((lambda (x) (quote (foo bar))) (list)) expr)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo-simple expr env store k val)]
         [(errorg 'cesk-empty-list-application-c "eval-expo-simple can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-empty-list-non-empty-answer-backwards-1"
   (run 1 (q)
     (fresh (expr k datum x y env^ env store val v-out)
       (== '(list) expr)
       (==
        `(application-inner-k
          (closure ,x (quote foo) ,env^)
          (empty-k)
          ,v-out)
        k)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((((list) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 'foo (_.5 _.6)) (empty-k) foo) foo)
      (=/= ((_.4 quote))) (sym _.4) (absento (list _.0) '_.5))))

 (test "cesk-empty-list-non-empty-answer-backwards-2"
   (run 7 (q)
     (fresh (expr k datum x y env^ env store val v-out a d)
       (== '(list) expr)
       (=/= '() val)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.4 . _.5) (_.6 . _.7)) (empty-k)) void) (num _.6) (sym _.4) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.4 . _.6) (_.7 _.8 . _.9)) (empty-k)) void) (=/= ((_.4 _.5))) (num _.7 _.8) (sym _.4 _.5) (absento (list _.0)))
     (((list) (_.0 _.1) _.2 (list-aux-inner-k _.3 (empty-k)) (_.3)) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 '_.5 (_.6 _.7)) (empty-k) _.5) _.5) (=/= ((_.4 quote)) ((_.5 ()))) (sym _.4) (absento (closure _.5) (list _.0) '_.6 (void _.5)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.6 _.4 . _.7) (_.8 _.9 _.10 . _.11)) (empty-k)) void) (=/= ((_.4 _.5)) ((_.4 _.6))) (num _.10 _.8 _.9) (sym _.4 _.5 _.6) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.4 . _.5) (_.6 . _.7)) (set!-k _.8 ((_.8 . _.9) (_.10 . _.11)) (empty-k))) void) (num _.10 _.6) (sym _.4 _.8) (absento (list _.0)))
     (((list) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 (lambda (_.5) _.6) (_.7 _.8)) (empty-k) (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8)))) (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8)))) (=/= ((_.4 lambda))) (num _.9) (sym _.4 _.5) (absento (_.9 _.2) (lambda _.7) (list _.0)))))

 (test "cesk-empty-list-non-empty-answer-backwards-b"
   (length
    (run 10 (q)
     (fresh (expr env store k val)
       (== '(list) expr)
       (=/= '() val)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo-simple
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo expr env store k val)]
         [(errorg 'cesk-empty-list-non-empty-answer-backwards-b "eval-expo can't handle state generated by eval-expo-simple:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-empty-list-non-empty-answer-backwards-c"
   (length
    (run 10 (q)
     (fresh (expr env store k val)
       (== '(list) expr)
       (=/= '() val)
       (== `(,expr ,env ,store ,k ,val) q)
       (eval-expo
        expr
        env
        store
        k
        val)
       (condu
         [(eval-expo-simple expr env store k val)]
         [(errorg 'cesk-empty-list-non-empty-answer-backwards-c "eval-expo-simple can't handle state generated by eval-expo:\n\n~s\n\n" q)]))))
   10)

 (test "cesk-nested-lists"
   (run 4 (q)
     (fresh (expr k datum x y env^ env store val v-out a d)
       (== '(list (list)) expr)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((((list (list)) (_.0 _.1) _.2 (empty-k) (())) (absento (list _.0)))
     (((list (list)) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.4 . _.5) (_.6 . _.7)) (empty-k)) void) (num _.6) (sym _.4) (absento (list _.0)))
     (((list (list)) (_.0 _.1) (_.2 _.3) (set!-k _.4 ((_.5 _.4 . _.6) (_.7 _.8 . _.9)) (empty-k)) void) (=/= ((_.4 _.5))) (num _.7 _.8) (sym _.4 _.5) (absento (list _.0)))
     (((list (list)) (_.0 _.1) _.2 (list-aux-inner-k _.3 (empty-k)) (_.3 ())) (absento (list _.0)))))

 (define quinec
   '((lambda (x)
       (list x (list (quote quote) x)))
     (quote
       (lambda (x)
         (list x (list (quote quote) x))))))

 (test "cesk-quinec-forwards"
   (run* (q)
     (evalo quinec q))
   `(,quinec))

 (test "cesk-quinec-both"
   (run 1 (q)
     (evalo quinec quinec))
   '(_.0))

 (test "cesk-quote-bkwards-0"
   (run 1 (q)
     (evalo (quote (quote x)) (quote x)))
   `(_.0))

 (test "cesk-quote-bkwards-1"
   (run 1 (q)
     (evalo `(quote (quote x)) `(quote x)))
   `(_.0))

 (test "cesk-quote-bkwards-2"
   (run 1 (q)
       (fresh (y)
         (== y 'x)
         (eval-expo `(quote ,y)
                    empty-env
                    empty-store
                    empty-k
                    q)))
   `(x))

 (test "cesk-quinec-bkwards-a"
   (run 1 (q)
     (== quinec q)
     (evalo q quinec))
   `(,quinec))

 (test "cesk-fresh-bkwards"
   (run 10 (q)
     (fresh (expr v)
       (evalo expr v)
       (== `(,expr ,v) q)))
   '((('_.0 _.0) (absento (closure _.0) (void _.0)))
     (((lambda (_.0) _.1) (closure _.0 _.1 (() ()))) (sym _.0))
     ((list) ())
     (((list '_.0) (_.0)) (absento (closure _.0) (void _.0)))
     (((list (lambda (_.0) _.1)) ((closure _.0 _.1 (() ())))) (sym _.0))
     ((((lambda (_.0) '_.1) '_.2) _.1) (=/= ((_.0 quote))) (sym _.0) (absento (closure _.1) (closure _.2) (void _.1) (void _.2)))
     ((((lambda (_.0) (lambda (_.1) _.2)) '_.3) (closure _.1 _.2 ((_.0) (_.4)))) (=/= ((_.0 lambda))) (num _.4) (sym _.0 _.1) (absento (closure _.3) (void _.3)))
     (((list '_.0 '_.1) (_.0 _.1)) (absento (closure _.0) (closure _.1) (void _.0) (void _.1)))
     ((((lambda (_.0) _.0) '_.1) _.1) (sym _.0) (absento (closure _.1) (void _.1)))
     ((((lambda (_.0) '_.1) (lambda (_.2) _.3)) _.1) (=/= ((_.0 quote))) (sym _.0 _.2) (absento (closure _.1) (void _.1)))))

 (test "cesk-quinec-bkwards-a"
   (run 50 (q)
     (fresh (expr env store k val)
       (eval-expo
        expr
        env
        store
        k
        val)
       (== `(,expr ,env ,store ,k ,val) q)))
   '((('_.0 (_.1 _.2) _.3 (empty-k) _.0) (absento (closure _.0) '_.1 (void _.0))) (((lambda (_.0) _.1) (_.2 _.3) _.4 (empty-k) (closure _.0 _.1 (_.2 _.3))) (sym _.0) (absento (lambda _.2))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.2 . _.4) (_.5 . _.6)) (empty-k) _.5) (num _.2) (sym _.0)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.5 . _.6) (_.7 . _.8)) (empty-k)) void) (num _.7) (sym _.5) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.2 . _.5) (_.6 _.7 . _.8)) (empty-k) _.7) (=/= ((_.2 _.4))) (num _.2 _.4) (sym _.0)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.6 _.5 . _.7) (_.8 _.9 . _.10)) (empty-k)) void) (=/= ((_.5 _.6))) (num _.8 _.9) (sym _.5 _.6) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.4 _.6 . _.7) (_.8 _.9 . _.10)) (empty-k) _.8) (=/= ((_.0 _.1))) (num _.3 _.4 _.6) (sym _.0 _.1)) (('_.0 (_.1 _.2) _.3 (list-aux-inner-k _.4 (empty-k)) (_.4 . _.0)) (absento (closure _.0) '_.1 (void _.0))) (((lambda (_.0) _.1) (_.2 _.3) (_.4 _.5) (set!-k _.6 ((_.6 . _.7) (_.8 . _.9)) (empty-k)) void) (num _.8) (sym _.0 _.6) (absento (lambda _.2))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10)) (empty-k) _.9) (=/= ((_.2 _.4)) ((_.2 _.5))) (num _.2 _.4 _.5) (sym _.0)) (((list) (_.0 _.1) _.2 (empty-k) ()) (absento (list _.0))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.2 . _.7) (_.8 _.9 _.10 _.11 . _.12)) (empty-k) _.11) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6))) (num _.2 _.4 _.5 _.6) (sym _.0)) ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.4 . _.7) (_.8 _.9 . _.10)) (empty-k) _.9) (=/= ((_.0 _.1)) ((_.4 _.6))) (num _.3 _.4 _.6) (sym _.0 _.1)) (('_.0 (_.1 _.2) (_.3 _.4) (application-inner-k (closure _.5 '_.6 (_.7 _.8)) (empty-k) _.6) _.6) (=/= ((_.5 quote))) (sym _.5) (absento (closure _.0) (closure _.6) '_.1 '_.7 (void _.0) (void _.6))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.2 . _.8) (_.9 _.10 _.11 _.12 _.13 . _.14)) (empty-k) _.13) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7))) (num _.2 _.4 _.5 _.6 _.7) (sym _.0)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.6 _.7 _.5 . _.8) (_.9 _.10 _.11 . _.12)) (empty-k)) void) (=/= ((_.5 _.6)) ((_.5 _.7))) (num _.10 _.11 _.9) (sym _.5 _.6 _.7) (absento (closure _.0) '_.1 (void _.0))) (((lambda (_.0) _.1) (_.2 _.3) (_.4 _.5) (set!-k _.6 ((_.7 _.6 . _.8) (_.9 _.10 . _.11)) (empty-k)) void) (=/= ((_.6 _.7))) (num _.10 _.9) (sym _.0 _.6 _.7) (absento (lambda _.2))) (((set! _.0 '_.1) ((_.0 . _.2) (_.3 . _.4)) (_.5 _.6) (empty-k) void) (=/= ((_.0 quote)) ((_.0 set!))) (num _.3) (sym _.0) (absento (closure _.1) '_.2 (set! _.2) (void _.1))) ((_.0 ((_.1 _.2 _.0 . _.3) (_.4 _.5 _.6 . _.7)) ((_.6 _.8 _.9 . _.10) (_.11 _.12 _.13 . _.14)) (empty-k) _.11) (=/= ((_.0 _.1)) ((_.0 _.2))) (num _.4 _.5 _.6 _.8 _.9) (sym _.0 _.1 _.2)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.5 . _.6) (_.7 . _.8)) (set!-k _.9 ((_.9 . _.10) (_.11 . _.12)) (empty-k))) void) (num _.11 _.7) (sym _.5 _.9) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.2 . _.9) (_.10 _.11 _.12 _.13 _.14 _.15 . _.16)) (empty-k) _.15) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8))) (num _.2 _.4 _.5 _.6 _.7 _.8) (sym _.0)) ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.7 _.4 . _.8) (_.9 _.10 _.11 . _.12)) (empty-k) _.11) (=/= ((_.0 _.1)) ((_.4 _.6)) ((_.4 _.7))) (num _.3 _.4 _.6 _.7) (sym _.0 _.1)) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.2 . _.10) (_.11 _.12 _.13 _.14 _.15 _.16 _.17 . _.18)) (empty-k) _.17) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0)) (('_.0 (_.1 _.2) (_.3 _.4) (application-inner-k (closure _.5 (lambda (_.6) _.7) (_.8 _.9)) (empty-k) (closure _.6 _.7 ((_.5 . _.8) (_.10 . _.9)))) (closure _.6 _.7 ((_.5 . _.8) (_.10 . _.9)))) (=/= ((_.5 lambda))) (num _.10) (sym _.5 _.6) (absento (_.10 _.3) (closure _.0) (lambda _.8) '_.1 (void _.0))) (((set! _.0 '_.1) ((_.2 _.0 . _.3) (_.4 _.5 . _.6)) (_.7 _.8) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!))) (num _.4 _.5) (sym _.0 _.2) (absento (closure _.1) '_.3 (set! _.3) (void _.1))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.10 _.2 . _.11) (_.12 _.13 _.14 _.15 _.16 _.17 _.18 _.19 . _.20)) (empty-k) _.19) (=/= ((_.10 _.2)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.10 _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0)) (((lambda (_.0) _.1) (_.2 _.3) _.4 (list-aux-inner-k _.5 (empty-k)) (_.5 closure _.0 _.1 (_.2 _.3))) (sym _.0) (absento (lambda _.2))) ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.7 _.8 _.4 . _.9) (_.10 _.11 _.12 _.13 . _.14)) (empty-k) _.13) (=/= ((_.0 _.1)) ((_.4 _.6)) ((_.4 _.7)) ((_.4 _.8))) (num _.3 _.4 _.6 _.7 _.8) (sym _.0 _.1)) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.2 . _.12) (_.13 _.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 . _.22)) (empty-k) _.21) (=/= ((_.10 _.2)) ((_.11 _.2)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.10 _.11 _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0)) (((set! _.0 (lambda (_.1) _.2)) ((_.0 . _.3) (_.4 . _.5)) (_.6 _.7) (empty-k) void) (=/= ((_.0 lambda)) ((_.0 set!))) (num _.4) (sym _.0 _.1) (absento (lambda _.3) (set! _.3))) ((_.0 ((_.1 _.2 _.0 . _.3) (_.4 _.5 _.6 . _.7)) ((_.8 _.6 _.9 . _.10) (_.11 _.12 _.13 . _.14)) (empty-k) _.12) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.6 _.8))) (num _.4 _.5 _.6 _.8 _.9) (sym _.0 _.1 _.2)) (((set! _.0 '_.1) ((_.2 _.3 _.0 . _.4) (_.5 _.6 _.7 . _.8)) (_.9 _.10) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!))) (num _.5 _.6 _.7) (sym _.0 _.2 _.3) (absento (closure _.1) '_.4 (set! _.4) (void _.1))) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.6 _.7 _.8 _.5 . _.9) (_.10 _.11 _.12 _.13 . _.14)) (empty-k)) void) (=/= ((_.5 _.6)) ((_.5 _.7)) ((_.5 _.8))) (num _.10 _.11 _.12 _.13) (sym _.5 _.6 _.7 _.8) (absento (closure _.0) '_.1 (void _.0))) (((lambda (_.0) _.1) (_.2 _.3) (_.4 _.5) (application-inner-k (closure _.6 '_.7 (_.8 _.9)) (empty-k) _.7) _.7) (=/= ((_.6 quote))) (sym _.0 _.6) (absento (closure _.7) (lambda _.2) '_.8 (void _.7))) (((lambda (_.0) _.1) (_.2 _.3) (_.4 _.5) (set!-k _.6 ((_.7 _.8 _.6 . _.9) (_.10 _.11 _.12 . _.13)) (empty-k)) void) (=/= ((_.6 _.7)) ((_.6 _.8))) (num _.10 _.11 _.12) (sym _.0 _.6 _.7 _.8) (absento (lambda _.2))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.2 . _.13) (_.14 _.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 . _.24)) (empty-k) _.23) (=/= ((_.10 _.2)) ((_.11 _.2)) ((_.12 _.2)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.10 _.11 _.12 _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.5 . _.6) (_.7 . _.8)) (set!-k _.9 ((_.10 _.9 . _.11) (_.12 _.13 . _.14)) (empty-k))) void) (=/= ((_.10 _.9))) (num _.12 _.13 _.7) (sym _.10 _.5 _.9) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.7 _.8 _.9 _.4 . _.10) (_.11 _.12 _.13 _.14 _.15 . _.16)) (empty-k) _.15) (=/= ((_.0 _.1)) ((_.4 _.6)) ((_.4 _.7)) ((_.4 _.8)) ((_.4 _.9))) (num _.3 _.4 _.6 _.7 _.8 _.9) (sym _.0 _.1)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.5 . _.6) (_.7 . _.8)) (list-aux-inner-k _.9 (empty-k))) (_.9 . void)) (num _.7) (sym _.5) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.2 . _.14) (_.15 _.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 . _.26)) (empty-k) _.25) (=/= ((_.10 _.2)) ((_.11 _.2)) ((_.12 _.2)) ((_.13 _.2)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.10 _.11 _.12 _.13 _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0)) (('_.0 (_.1 _.2) (_.3 _.4) (set!-k _.5 ((_.6 _.5 . _.7) (_.8 _.9 . _.10)) (set!-k _.11 ((_.11 . _.12) (_.13 . _.14)) (empty-k))) void) (=/= ((_.5 _.6))) (num _.13 _.8 _.9) (sym _.11 _.5 _.6) (absento (closure _.0) '_.1 (void _.0))) (('_.0 (_.1 _.2) (_.3 _.4) (list-aux-inner-k _.5 (set!-k _.6 ((_.6 . _.7) (_.8 . _.9)) (empty-k))) void) (num _.8) (sym _.6) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.2 . _.4) (_.5 . _.6)) (set!-k _.7 ((_.7 . _.8) (_.9 . _.10)) (empty-k)) void) (num _.2 _.9) (sym _.0 _.7)) (((lambda (_.0) _.1) (_.2 _.3) (_.4 _.5) (set!-k _.6 ((_.6 . _.7) (_.8 . _.9)) (set!-k _.10 ((_.10 . _.11) (_.12 . _.13)) (empty-k))) void) (num _.12 _.8) (sym _.0 _.10 _.6) (absento (lambda _.2))) (('_.0 (_.1 _.2) _.3 (list-aux-outer-k (_.4) _.5 (empty-k) ()) (_.0)) (absento (closure _.0) '_.1 (void _.0))) ((_.0 ((_.1 _.2 _.3 _.0 . _.4) (_.5 _.6 _.7 _.8 . _.9)) ((_.8 _.10 _.11 _.12 . _.13) (_.14 _.15 _.16 _.17 . _.18)) (empty-k) _.14) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3))) (num _.10 _.11 _.12 _.5 _.6 _.7 _.8) (sym _.0 _.1 _.2 _.3)) (((set! _.0 '_.1) ((_.2 _.3 _.4 _.0 . _.5) (_.6 _.7 _.8 _.9 . _.10)) (_.11 _.12) (empty-k) void) (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)) ((_.4 quote)) ((_.4 set!))) (num _.6 _.7 _.8 _.9) (sym _.0 _.2 _.3 _.4) (absento (closure _.1) '_.5 (set! _.5) (void _.1))) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.2 . _.15) (_.16 _.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 . _.28)) (empty-k) _.27) (=/= ((_.10 _.2)) ((_.11 _.2)) ((_.12 _.2)) ((_.13 _.2)) ((_.14 _.2)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.10 _.11 _.12 _.13 _.14 _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0)) ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.7 _.8 _.9 _.10 _.4 . _.11) (_.12 _.13 _.14 _.15 _.16 _.17 . _.18)) (empty-k) _.17) (=/= ((_.0 _.1)) ((_.10 _.4)) ((_.4 _.6)) ((_.4 _.7)) ((_.4 _.8)) ((_.4 _.9))) (num _.10 _.3 _.4 _.6 _.7 _.8 _.9) (sym _.0 _.1)) ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.9 _.10 _.11 _.12 _.13 _.14 _.15 _.2 . _.16) (_.17 _.18 _.19 _.20 _.21 _.22 _.23 _.24 _.25 _.26 _.27 _.28 _.29 . _.30)) (empty-k) _.29) (=/= ((_.10 _.2)) ((_.11 _.2)) ((_.12 _.2)) ((_.13 _.2)) ((_.14 _.2)) ((_.15 _.2)) ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)) ((_.2 _.9))) (num _.10 _.11 _.12 _.13 _.14 _.15 _.2 _.4 _.5 _.6 _.7 _.8 _.9) (sym _.0))))

 (test "cesk-quinec-bkwards-c"
   (run 10 (q)
     (evalo q quinec))
   '('((lambda (x) (list x (list 'quote x)))
     '(lambda (x) (list x (list 'quote x))))
   (list
     '(lambda (x) (list x (list 'quote x)))
     ''(lambda (x) (list x (list 'quote x))))
   (((lambda (_.0)
       '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
   (((lambda (_.0) _.0)
      '((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x)))))
     (sym _.0))
   (((lambda (_.0)
       '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      (lambda (_.1) _.2))
     (=/= ((_.0 quote)))
     (sym _.0 _.1))
   (list
     '(lambda (x) (list x (list 'quote x)))
     (list 'quote '(lambda (x) (list x (list 'quote x)))))
   (((lambda (_.0)
       (list
         '(lambda (x) (list x (list 'quote x)))
         ''(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 list)) ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
   (((lambda (_.0)
       ((lambda (_.1)
          '((lambda (x) (list x (list 'quote x)))
             '(lambda (x) (list x (list 'quote x)))))
         '_.2))
      '_.3)
     (=/= ((_.0 lambda)) ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (closure _.3) (void _.2) (void _.3)))
   ((list
      '(lambda (x) (list x (list 'quote x)))
      ((lambda (_.0) ''(lambda (x) (list x (list 'quote x))))
        '_.1))
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
   (((lambda (_.0)
       '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      (list))
     (=/= ((_.0 quote)))
     (sym _.0))))

 (test "cesk-quinec-for-real"
   (run 1 (q)
     (evalo q q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0)))
       '(lambda (_.0) (list _.0 (list 'quote _.0))))
      (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)) ((_.0 void)))
      (sym _.0))))

 (test "cesk-hard-quinec-bkwards-b"
   (run 1 (q)
     (evalo q quinec)
     (== quinec q))
   `(,quinec))

 (test "twines"
   (run 1 (r)
     (fresh (p q)
       (=/= p q)
       (evalo p q)
       (evalo q p)
       (== `(,p ,q) r)))
   '((('((lambda (_.0)
           (list 'quote (list _.0 (list 'quote _.0))))
         '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
       ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
        '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
      (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)) ((_.0 void)))
      (sym _.0))))

 (test "cesk-quinec-for-real-3"
   (run 3 (q)
     (evalo q q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0))) '(lambda (_.0) (list _.0 (list 'quote _.0)))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)) ((_.0 void))) (sym _.0))
     (((lambda (_.0) (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))) '(lambda (_.0) (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.0 void)) ((_.1 closure)) ((_.1 quote)) ((_.1 void))) (sym _.0 _.1) (absento (closure _.2) (void _.2)))
     (((lambda (_.0) (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2))) '(lambda (_.0) (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2)))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.0 void)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)) ((_.1 void))) (sym _.0 _.1) (absento (closure _.2) (void _.2)))))

 #!eof

 ;;; comes back under full chez in about 48 seconds
 ;;; would probably be waiting at least 3x as long under petite, if it doesn't run out of memory.
 (test "thrine"
   (run 1 (x)
     (fresh (p q r)
       (=/= p q)
       (=/= q r)
       (=/= r p)
       (evalo p q)
       (evalo q r)
       (evalo r p)
       (== `(,p ,q ,r) x)))
   '(((''((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
       '((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
       ((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))))
      (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)) ((_.0 void)))
      (sym _.0))))

;;; took eight minutes to find this under full chez with optimize-level 3 on casper (with only set! added to the quines language, not call/cc)
 (test "quine-with-set!"
   (run 1 (q)
     (evalo q q)
     (fails-unless-contains q 'set!))
   '((((lambda (_.0)
         (list
          _.0
          (list ((lambda (_.1) 'quote) (set! _.0 _.0)) _.0)))
       '(lambda (_.0)
          (list
           _.0
           (list ((lambda (_.1) 'quote) (set! _.0 _.0)) _.0))))
      (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote))
           ((_.0 set!)) ((_.0 void)) ((_.1 closure)) ((_.1 quote))
           ((_.1 void)))
      (sym _.0 _.1))))
|#

  ))

(provide
  (all-defined-out)
  (all-from-out cKanren/miniKanren))

