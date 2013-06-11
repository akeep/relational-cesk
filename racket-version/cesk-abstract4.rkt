#lang racket

;; setup the state to maintain the pointers in the backwards direction so that
;; we can create an immutable state that we can use in sets and that we can
;; more easily translate into a relational program.
(struct state
  (exp env store k* time)
  #:constructor-name make-state
  #:inspector (make-inspector))

;; go ahead and represent the environment as a pair of parallel lists that
;; contain variables (in the first list) and locations (in the second list)
(define empty-env '(() . ()))

(define extend-env
  (lambda (x loc env)
    (cons (cons x (car env)) (cons loc (cdr env)))))

(define apply-env
  (lambda (env x)
    (let loop ((x* (car env)) (loc* (cdr env)))
      (cond
        ((null? x*) (error 'apply-env "~s is not bound in the environment" x))
        ((eq? x (car x*)) (car loc*))
        (else (loop (cdr x*) (cdr loc*)))))))

;; go ahead and represent the store as a pair of parallel lists that contain
;; locations (in the first list) and sets of values/continuations (in the
;; second list)
(define empty-store '(() . ()))

(define extend-store
  (lambda (loc val store)
    (let loop ((loc* (car store))
               (val-set* (cdr store))
               (rloc* '())
               (rval-set* '()))
      (cond
        ((null? loc*)
         (cons
           (cons loc (reverse rloc*))
           (cons (set val) (reverse rval-set*))))
        ((equal? loc (car loc*))
         (cons
           (append (reverse rloc*) loc*)
           (append (reverse rval-set*)
             (cons (set-add (car val-set*) val) (cdr val-set*)))))
        (else
          (loop
            (cdr loc*)
            (cdr val-set*)
            (cons (car loc*) rloc*)
            (cons (car val-set*) rval-set*)))))))

(define apply-store
  (lambda (store loc)
    (let loop ((loc* (car store)) (val-set* (cdr store)))
      (cond
        ((null? loc*) (error 'apply-store "~s is not bound in the store" loc))
        ((equal? loc (car loc*)) (car val-set*))
        (else (loop (cdr loc*) (cdr val-set*)))))))

;; alloc adds the time and the label of the state expression
(define alloc
  (lambda (state)
    (cons (state-time state) (car (state-exp state)))))

(define lookup
  (lambda (env store x)
    (apply-store store (apply-env env x))))

(define empty-time '())

; limit the length of the time
(define time-limit 1)

(define tick
  (lambda (state)
    (let ((time (state-time state)))
      (if (= time-limit 0)
          time
          (cons (car (state-exp state)) (take time (- time-limit 1)))))))

(define empty-k '(empty-k))

(define if-k
  (lambda (c a env k*)
    `(if-k ,c ,a ,env ,k*)))

(define call/cc-k
  (lambda (k*)
    `(call/cc-k ,k*)))

(define throw-k
  (lambda (v-e env)
    `(throw-k ,v-e ,env)))

(define set!-k
  (lambda (x env k*)
    `(set!-k ,x ,env ,k*)))

(define begin-k
  (lambda (e2 env k*)
    `(begin-k ,e2 ,env ,k*)))

(define application-inner-k
  (lambda (p* k*)
    `(application-inner-k ,p* ,k*)))

(define application-outer-k
  (lambda (rand env k*)
    `(application-outer-k ,rand ,env ,k*)))

(define list-aux-inner-k
  (lambda (loc k*)
    `(list-aux-inner-k ,loc ,k*)))

(define list-aux-outer-k
  (lambda (e* env k*)
    `(list-aux-outer-k ,e* ,env ,k*)))

(define make-continuation
  (lambda (k*)
    `(continuation ,k*)))

(define apply-k*
  (lambda (state vs wl seen-states state-adjacency)
    (let loop ((ks (apply-store (state-store state) (state-k* state)))
               (wl wl)
               (state-adjacency state-adjacency))
      (if (set-empty? ks)
          (values wl state-adjacency)
          (let ((k (set-first ks)) (ks (set-rest ks)))
            (match k
              (`(empty-k) (loop ks wl state-adjacency))
              (`(call/cc-k ,k*)
                (let-values (((wl state-adjacency)
                              (apply-proc vs (set (make-continuation k*))
                                k* state wl seen-states state-adjacency)))
                  (loop ks wl state-adjacency)))
              (`(if-k ,c ,a ,env ,k*)
                (let inner-loop ((vs vs) (wl wl) (state-adjacency state-adjacency))
                  (if (set-empty? vs)
                      (loop ks wl state-adjacency)
                      (let-values (((wl state-adjacency)
                                    (add-next-state wl state seen-states state-adjacency
                                      (make-state (if (set-first vs) c a) env (state-store state)
                                        k* (tick (state-time state))))))
                        (inner-loop (set-rest vs) wl state-adjacency)))))
              (`(set!-k ,x ,env ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let ((loc (apply-env env x)))
                  (let inner-loop ((vs vs) (wl wl) (state-adjacency state-adjacency))
                    (if (set-empty? vs)
                        (loop ks wl state-adjacency)
                        (let ((v (set-first vs)))
                          (if (value? v)
                              (let ((store^ (extend-store loc v
                                              (state-store state))))
                                (let-values (((wl state-adjacency)
                                              (add-next-state wl state seen-states state-adjacency
                                                (make-state (void) env store^ k* (tick state)))))
                                  (inner-loop (set-rest vs) wl state-adjacency)))
                              (inner-loop (set-rest vs) wl state-adjacency)))))))
              (`(begin-k ,e2 ,env ,k*)
                (if (set-empty? vs)
                    (loop ks wl state-adjacency)
                    (let-values (((wl state-adjacency)
                                  (add-next-state wl state seen-states state-adjacency
                                    (make-state e2 env (state-store state) k* (tick state)))))
                      (loop ks wl state-adjacency))))
              (`(application-inner-k ,p* ,k*)
                (let-values (((wl state-adjacency)
                              (apply-proc p* vs k* state wl seen-states state-adjacency)))
                  (loop ks wl state-adjacency)))
              (`(application-outer-k ,rand ,env ,k*)
                (let* ((k*^ (alloc state))
                       (store^ (extend-store k*^
                                 (application-inner-k vs k*)
                                 (state-store state))))
                  (let-values (((wl state-adjacency)
                                (add-next-state wl state seen-states state-adjacency
                                  (make-state rand env store^ k*^ (tick state)))))
                    (loop ks wl state-adjacency))))
              (`(list-aux-inner-k ,a ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl) (state-adjacency state-adjacency))
                  (if (set-empty? vs)
                      (loop ks wl state-adjacency)
                      (let ((v (set-first vs)))
                        (if (list? v)
                            (let* ((loc (alloc state))
                                   (store^ (extend-store loc a
                                             (state-store state))))
                              (let-values (((wl state-adjacency)
                                            (add-next-state wl state seen-states state-adjacency
                                              (make-state `(quote ,(cons loc v)) (state-env state)
                                                store^ k* (tick state)))))
                                (inner-loop (set-rest vs) wl state-adjacency)))
                            (inner-loop (set-rest vs) wl state-adjacency))))))
              (`(list-aux-outer-k ,e* ,env ,k*)
                (let inner-loop ((vs vs) (wl wl) (state-adjacency state-adjacency))
                  (if (set-empty? vs)
                      (loop ks wl state-adjacency)
                      (let ((v (set-first vs)))
                        (if (value? v)
                            (let* ((k*^ (alloc state))
                                   (store^ (extend-store k*^
                                             (list-aux-inner-k v k*)
                                             (state-store state))))
                              (let-values (((wl state-adjacency)
                                            (list-aux e*
                                              (make-state e* env store^ k*^ (tick state))
                                              wl seen-states state-adjacency)))
                                (inner-loop (set-rest vs) wl state-adjacency)))
                            (inner-loop (set-rest vs) wl state-adjacency))))))
              ; we found a non-continuation at k*, so just ignore it.
              (_ (loop ks wl state-adjacency))))))))

(define make-closure
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define apply-proc
  (lambda (ps as k* state wl seen-states state-adjacency)
    (let loop ((ps ps) (wl wl) (state-adjacency state-adjacency))
      (if (set-empty? ps)
          (values wl state-adjacency)
          (let ((p (set-first ps)))
            (match p
              (`(closure ,x ,body ,env)
                (let inner-loop ((as as) (wl wl) (state-adjacency state-adjacency))
                  (if (set-empty? as)
                      (loop (set-rest ps) wl state-adjacency)
                      (let ((a (set-first as)))
                        (if (value? a)
                            (let* ((loc (alloc state))
                                   (env^ (extend-env x loc env))
                                   (store^ (extend-store loc a
                                             (state-store state))))
                              (let-values (((wl state-adjacency)
                                            (add-next-state wl state seen-states state-adjacency
                                              (make-state body env^ store^ k* (tick state)))))
                                (inner-loop (set-rest as) wl state-adjacency)))
                            (inner-loop (set-rest as) wl state-adjacency))))))
              (`(continuation ,k*)
                (let inner-loop ((as as) (wl wl) (state-adjacency state-adjacency))
                  (if (set-empty? as)
                      (loop (set-rest ps) wl state-adjacency)
                      (let ((a (set-first as)))
                        (if (value? a)
                            (let-values (((wl state-adjacency)
                                          (add-next-state wl state seen-states state-adjacency
                                            (make-state `(quote ,a) (state-env state)
                                              (state-store state) k* (tick state)))))
                              (inner-loop (set-rest as) wl state-adjacency))
                            (inner-loop (set-rest as) wl state-adjacency))))))
              (_ (loop (set-rest ps) wl state-adjacency))))))))

(define add-next-state
  (lambda (wl state seen-states state-adjacency new-state)
    (let ((state-adjacency (set-add state-adjacency (cons state new-state))))
      (if (set-member? seen-states new-state)
          (values wl state-adjacency)
          (values (set-add wl new-state) state-adjacency)))))

(define value?
  (lambda (x)
    (or (void? x)
        (number? x)
        (boolean? x)
        (symbol? x)
        ;; technically we can have more here, since we have quote in the language.
        (match x
          (`(closure ,x ,body ,env) #t)
          (`(continuation ,k*) #t)
          ; the following is not exactly safe because our continuations are tagged lists.
          (`(,kw ,rest* ...)
            (not (memq kw '(empty-k if-k zero?-k sub1-k subtraction-inner-k
                            subtraction-outer-k call/cc-k throw-k
                            addition-inner-k addition-outer-k
                            multiplication-inner-k multiplication-outer-k
                            set!-k begin-k application-inner-k
                            application-outer-k list-aux-inner-k
                            list-aux-outer-k))))))))

;; note: not using not-in-env because variables are renamed previous to
;; abstract interpretation.
(define abs-interp-aux
  (lambda (wl seen-states state-adjacency)
    (if (set-empty? wl)
        (values seen-states state-adjacency)
        (let* ((state (set-first wl))
               (wl (set-rest wl))
               (seen-states (set-add seen-states state)))
          (match (cdr (state-exp state))
            (`(quote ,d)
              (let-values (((wl state-adjacency)
                            (apply-k* state (set d) wl seen-states state-adjacency)))
                (abs-interp-aux wl seen-states state-adjacency)))
            ((? symbol? x)
             (let-values (((wl state-adjacency)
                           (apply-k* state
                             (lookup (state-env state) (state-store state) x)
                             wl seen-states state-adjacency)))
               (abs-interp-aux wl seen-states state-adjacency)))
            (`(if ,t ,c ,a)
              (let* ((env (state-env state))
                      (k*^ (alloc state))
                      (store^ (extend-store k*^
                                (if-k c a env (state-k* state))
                                (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state t env store^ k*^ (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency))))
            (`(call/cc ,e)
              (let* ((k*^ (alloc state))
                      (store^ (extend-store k*^
                                (call/cc-k (state-k* state))
                                (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state e (state-env state) store^ k*^ (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency))))
            (`(throw ,cc-e ,v-e)
              (let* ((env (state-env state))
                      (k*^ (alloc state))
                      (store^ (extend-store k*^
                                (throw-k v-e env)
                                (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state cc-e env store^ k*^ (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency))))
            (`(letcc ,x ,body)
              (let* ((loc (alloc state))
                      (k* (state-k* state))
                      (env^ (extend-env x loc (state-env state)))
                      (store^ (extend-store loc
                                (make-continuation k*)
                                (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state body env^ store^ k* (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency))))
            (`(lambda (,x) ,body)
              (let-values (((wl state-adjacency)
                            (apply-k* state (set (make-closure x body (state-env state)))
                              wl seen-states state-adjacency)))
                (abs-interp-aux wl seen-states state-adjacency)))
            (`(set! ,x ,rhs)
              (let* ((env (state-env state))
                      (k*^ (alloc state))
                      (store^ (extend-store k*^
                                (set!-k x env (state-k* state))
                                (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state rhs env store^ k*^ (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency))))
            (`(begin ,e1 ,e2)
              (let* ((env (state-env state))
                     (k*^ (alloc state))
                     (store^ (extend-store k*^
                               (begin-k e2 env (state-k* state))
                               (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state e1 env store^ k*^ (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency))))
            (`(list . ,e*) 
              (let-values (((wl state-adjacency)
                            (list-aux e* state wl seen-states state-adjacency)))
                (abs-interp-aux wl seen-states state-adjacency)))
            (`(,rator ,rand)
              (let* ((env (state-env state))
                      (k*^ (alloc state))
                      (store^ (extend-store k*^
                                (application-outer-k rand env (state-k* state))
                                (state-store state))))
                (let-values (((wl state-adjacency)
                              (add-next-state wl state seen-states state-adjacency
                                (make-state rator env store^ k*^ (tick state)))))
                  (abs-interp-aux wl seen-states state-adjacency)))))))))

(define list-aux
  (lambda (e* state wl seen-states state-adjacency)
    (if (null? e*)
        (apply-k* state (set '()) wl seen-states state-adjacency)
        (let* ((env (state-env state))
               (k*^ (alloc state))
               (store^ (extend-store k*^
                         (list-aux-outer-k (cdr e*) env (state-k* state))
                         (state-store state))))
          (add-next-state wl state seen-states state-adjacency
            (make-state (car e*) env k*^ store^ (tick state)))))))

(define abstract-interpret
  (lambda (e)
    ;; setup our default store and k* (cheat a little here since we pass the
    ;; state to the alloc function, but we need the the first allocation to
    ;; bootstrap our state).
    (let* ((k* e)
           (store (extend-store k* empty-k empty-store))
           (initial-state (make-state e empty-env store k* empty-time)))
      (abs-interp-aux (set initial-state) (set) (set)))))

(define walk*-v
  (lambda (v s)
    (match v
      ((? symbol? x) x) ; quoted symbol
      ((? boolean? b) b)
      ((? number? n) n)
      ; empty list (created with either quote or list--doesn't matter)
      (`() '())
      ; quoted list (case 1) (can't overlap with a list of nums)
      (`(,(? (lambda (x)
               (and (not (number? x))
                    (not (eq? 'closure x))
                    (not (eq? 'continuation x))))
            a) . ,d)
       `(,a . ,d))
      ; quoted list (case 2) (can't overlap with a list of nums)
      (`((,aa . ,ad) . ,d) `((,aa . ,ad) . ,d))
      ;;; arguably I should walk* the body as well, although this could cause
      ;;; its own problems.  although if procedures are opaque, the user really
      ;;; has no right to look inside
      (`(closure ,x ,body ,env)
       `(closure ,x ,body ,env))
      ;;; arguably should also walk components of continuations that might
      ;;; contain values
      (`(continuation ,k*)
        (apply-store s k*))
      (`(,(? number? addr) . ,addr*) ; non-empty list
       (map-lookup-address `(,addr . ,addr*) s)))))

(define map-lookup-address
  (lambda (addr* s)
    (match addr*
      (`() '())
      (`(,(? number? addr) . ,addr-res)
       (let ((t (apply-store s addr)))
         (let ((v (walk*-v t s)))
           (cons v (map-lookup-address addr-res s))))))))

(define state->dot
  (lambda (state-set state-adjacency)
    (let ((ht (make-hasheq)) (num 0))
      (define (next-num) (begin0 num (set! num (+ num 1))))
      (define (visited? s) (and (hash-ref ht s #f) #t))
      (define (state->pretty-name state)
        (let ((pn (hash-ref ht state #f)))
          (or pn (let ((pn (string-append "s_" (number->string (next-num)))))
                   (hash-set! ht state pn)
                   pn))))
      (define (state->subscript-name s)
        (let ((s (state->pretty-name s)))
          (string-append "<s<sub>" (substring s 2 (string-length s)) "</sub>>")))
      (define (pretty-print-state s)
        (unless (visited? s)
          (display "  ")
          (display (state->pretty-name s))
          (display " [label=")
          (display (state->subscript-name s))
          (display "];")
          (newline)))
      (display "digraph {")
      (newline)
      (let loop ((wl state-adjacency))
        (if (set-empty? wl)
            (begin
              (display "}")
              (newline)
              (newline)
              (set-for-each state-set
                (lambda (state)
                  (display (state->pretty-name state))
                  (display ":")
                  (newline)
                  (display "  exp: ")
                  (write (state-exp state))
                  (newline)
                  (display "  env: ")
                  (write (state-env state))
                  (newline)
                  (display "  store: ")
                  (write (state-store state))
                  (newline)
                  (display "  k*: ")
                  (write (state-k* state))
                  (newline)
                  (display "  time: ")
                  (write (state-time state))
                  (newline)
                  (newline))))
            (let ((adj (set-first wl)) (wl (set-rest wl)))
              (let ((ps (car adj)) (cs (cdr adj)))
                (pretty-print-state ps)
                (pretty-print-state cs)
                (display "  ")
                (display (state->pretty-name ps))
                (display " -> ")
                (display (state->pretty-name cs))
                (display ";")
                (newline)
                (loop wl))))))))

(define label-expressions
  (lambda (exp)
    (define next-label
      (let ((count 0))
        (lambda ()
          (let ((c count))
            (set! count (+ count 1))
            (string->symbol (string-append "l." (number->string c)))))))
    (let f ((exp exp))
      (match exp
        ((? number? n) (cons (next-label) exp))
        ((? boolean? b) (cons (next-label) exp))
        ((? symbol? x) (cons (next-label) exp))
        (`(quote ,datum) (cons (next-label) exp))
        (`(if ,t ,c ,a) (cons (next-label) `(if ,(f t) ,(f c) ,(f a))))
        (`(zero? ,e) (cons (next-label) `(zero? ,(f e))))
        (`(sub1 ,e) (cons (next-label) `(sub1 ,(f e))))
        (`(- ,e1 ,e2) (cons (next-label) `(- ,(f e1) ,(f e2))))
        (`(+ ,e1 ,e2) (cons (next-label) `(+ ,(f e1) ,(f e2))))
        (`(* ,e1 ,e2) (cons (next-label) `(* ,(f e1) ,(f e2))))
        (`(call/cc ,e) (cons (next-label) `(call/c ,(f e))))
        (`(throw ,cc-e ,v-e) (cons (next-label) `(throw ,(f cc-e) ,(f v-e))))
        (`(letcc ,x ,body) (cons (next-label) `(letcc ,x ,(f body))))
        (`(lambda (,x) ,body) (cons (next-label) `(lambda (,x) ,(f body))))
        (`(set! ,x ,rhs) (cons (next-label) `(set! ,x ,(f rhs))))
        (`(begin ,e1 ,e2) (cons (next-label) `(begin ,(f e1) ,(f e2))))
        (`(list . ,e*) (cons (next-label) `(list . ,(map f e*))))
        (`(,rator ,rand) (cons (next-label) `(,(f rator) ,(f rand))))))))

(define rename-variables
  (lambda (exp)
    (define unique-name
      (let ((count 0))
        (lambda (x)
          (let ((c count))
            (set! count (+ count 1))
            (string->symbol
              (string-append
                (symbol->string x)
                "."
                (number->string c)))))))
    (define replace
      (lambda (x env)
        (cond
          ((assq x env) => cdr)
          (else (error 'rename-variables "unbound variable ~s" x)))))
    (define not-in-env
      (lambda (x env)
        (not (assq x env))))
    (define valid-keyword?
      (lambda (kw env)
        (lambda (x)
          (and (eq? x kw) (not-in-env kw env)))))
    (let f ((exp exp) (env '()))
      (match exp
        ((? number? n) n)
        ((? boolean? b) b)
        ((? symbol? x) (replace x env))
        (`(,(? (valid-keyword? 'quote env) _) ,datum) `(quote ,datum))
        (`(,(? (valid-keyword? 'if env) _) ,t ,c ,a)
          `(if ,(f t env) ,(f c env) ,(f a env)))
        (`(,(? (valid-keyword? 'zero? env) _) ,e) `(zero? ,(f e env)))
        (`(,(? (valid-keyword? 'sub1 env) _) ,e) `(sub1 ,(f e env)))
        (`(,(? (valid-keyword? '- env) _) ,e1 ,e2) `(- ,(f e1 env) ,(f e2 env)))
        (`(,(? (valid-keyword? '+ env) _) ,e1 ,e2) `(+ ,(f e1 env) ,(f e2 env)))
        (`(,(? (valid-keyword? '* env) _) ,e1 ,e2) `(* ,(f e1 env) ,(f e2 env)))
        (`(,(? (valid-keyword? 'call/cc env) _) ,e) `(call/cc ,(f e env)))
        (`(,(? (valid-keyword? 'throw env) _) ,cc-e ,v-e)
          `(throw ,(f cc-e env) ,(f v-e env)))
        (`(,(? (valid-keyword? 'letcc env) _) ,cc ,body)
         (let ((t (unique-name cc)))
           `(letcc ,t ,(f body (cons (cons cc t) env)))))
        (`(,(? (valid-keyword? 'lambda env) _) (,x) ,body)
          (let ((t (unique-name x)))
            `(lambda (,t) ,(f body (cons (cons x t) env)))))
        (`(,(? (valid-keyword? 'set! env) _) ,x ,rhs)
          `(set! ,(replace x env) ,(f x env)))
        (`(,(? (valid-keyword? 'begin env) _) ,e1 ,e2)
          `(begin ,(f e1 env) ,(f e2 env)))
        (`(,(? (valid-keyword? 'list env) _) . ,e*)
          `(list ,@(map (lambda (e) (f e env)) e*)))
        (`(,rator ,rand) `(,(f rator env) ,(f rand env)))))))

(provide (all-defined-out))

