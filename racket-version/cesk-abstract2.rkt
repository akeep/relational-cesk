#lang racket

(struct state
  (exp env store k* time (next-states #:mutable #:auto))
  #:auto-value '()
  #:constructor-name make-state)

(define state=?
  (lambda (state1 state2)
    (or (eq? state1 state2)
        (and (and (state? state1) (state? state2))
             (eq? (state-exp state1) (state-exp state2))
             (equal? (state-env state1) (state-env state2))
             (equal? (state-k* state1) (state-k* state2))
             (equal? (state-time state1) (state-time state2))))))

(define state-set-includes?
  (lambda (state state-set)
    (memf (lambda (s) (state=? s state)) state-set)))

(define empty-env '())

(define extend-env
  (lambda (x loc env)
    (cons (cons x loc) env)))

(define apply-env
  (lambda (env x)
    (cond
      ((assq x env) => cdr)
      (else (error 'apply-env "~s is not bound in the environment" x)))))

(define empty-store '())

(define alloc
  (lambda (state)
    (cons (state-time state) (state-exp state))))

(define extend-store
  (lambda (loc val store)
    (let loop ((store store))
      (cond
        ((null? store) (list (cons loc (set val))))
        ((equal? loc (caar store))
         (cons (cons loc (set-add (cdar store) val)) (cdr store)))
        (else (cons (car store) (loop (cdr store))))))))

(define apply-store
  (lambda (store loc)
    (cond
      ((assoc loc store) => cdr)
      (else (error 'apply-store "address '~s' not found in store" loc)))))

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
          (cons (state-k* state) (take time (- time-limit 1)))))))

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
  (lambda (state vs wl seen-states)
    (let loop ((ks (apply-store (state-store state) (state-k* state)))
               (wl wl))
      (if (set-empty? ks)
          (abs-interp-aux! wl seen-states)
          (let ((k (set-first ks)) (ks (set-rest ks)))
            (match k
              (`(empty-k) (loop ks wl))
              (`(call/cc-k ,k*)
                (loop ks
                  (apply-proc vs (set (make-continuation k*))
                    k* state wl seen-states)))
              (`(if-k ,c ,a ,env ,k*)
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (add-next-state! wl state seen-states
                          (make-state (if (set-first vs) c a) env (state-store state)
                            k* (tick (state-time state))))))))
              (`(zero?-k ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (add-next-state! wl state seen-states
                                (make-state (zero? v) (state-env state)
                                  (state-store state) k* (tick state)))
                              wl))))))
              (`(sub1-k ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (add-next-state! wl state seen-states
                                (make-state (sub1 v) (state-env state)
                                  (state-store state) k* (tick state)))
                              wl))))))
              (`(subtraction-inner-k ,v1 ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (add-next-state! wl state seen-states
                                (make-state (- v1 v) (state-env state)
                                  (state-store state) k* (tick state)))
                              wl))))))
              (`(subtraction-outer-k ,e2 ,env ,k*)
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (let* ((k*^ (alloc state))
                                     (store^ (extend-store k*^
                                              (subtraction-inner-k v k*)
                                              (state-store state))))
                                (add-next-state! wl state seen-states
                                  (make-state e2 env store^ k*^ (tick state))))
                              wl))))))
              (`(addition-inner-k ,v1 ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (add-next-state! wl state seen-states
                                (make-state (+ v1 v) (state-env state)
                                  (state-store state) k* (tick state)))
                              wl))))))
              (`(addition-outer-k ,e2 ,env ,k*)
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (let* ((k*^ (alloc state))
                                     (store^ (extend-store k*^
                                              (addition-inner-k v k*)
                                              (state-store state))))
                                (add-next-state! wl state seen-states
                                  (make-state e2 env store^ k*^ (tick state))))
                              wl))))))
              (`(multiplication-inner-k ,v1 ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (add-next-state! wl state seen-states
                                (make-state (* v1 v) (state-env state)
                                  (state-store state) k* (tick state)))
                              wl))))))
              (`(multiplication-outer-k ,e2 ,env ,k*)
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (number? v)
                              (let* ((k*^ (alloc state))
                                     (store^ (extend-store k*^
                                              (multiplication-inner-k v k*)
                                              (state-store state))))
                                (add-next-state! wl state seen-states
                                  (make-state e2 env store^ k*^ (tick state))))
                              wl))))))
              (`(set!-k ,x ,env ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let ((loc (apply-env env x)))
                  (let inner-loop ((vs vs) (wl wl))
                    (if (set-empty? vs)
                        (loop ks wl)
                        (inner-loop (set-rest vs)
                          (let ((v (set-first vs)))
                            (if (value? v)
                                (let ((store^ (extend-store loc v
                                                (state-store state))))
                                  (add-next-state! wl state seen-states
                                    (make-state (void) env store^ k* (tick state))))
                                wl)))))))
              (`(begin-k ,e2 ,env ,k*)
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (add-next-state! wl state seen-states
                        (make-state e2 env (state-store state) k* (tick state))))))
              (`(application-inner-k ,p* ,k*)
                (loop ks (apply-proc p* vs k* state wl seen-states)))
              (`(application-outer-k ,rand ,env ,k*)
                (let* ((k*^ (alloc state))
                       (store^ (extend-store k*^
                                 (application-inner-k vs k*)
                                 (state-store state))))
                  (loop ks (add-next-state! wl state seen-states
                             (make-state rand env store^ k*^ (tick state))))))
              (`(list-aux-inner-k ,a ,k*)
                ;; no simple alternative to adding to the work-list here.
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (list? v)
                              (let* ((loc (alloc state))
                                     (store^ (extend-store loc a
                                               (state-store state))))
                                (add-next-state! wl state seen-states
                                  (make-state `(quote ,(cons loc v)) (state-env state)
                                    store^ k* (tick state))))
                              wl))))))
              (`(list-aux-outer-k ,e* ,env ,k*)
                (let inner-loop ((vs vs) (wl wl))
                  (if (set-empty? vs)
                      (loop ks wl)
                      (inner-loop (set-rest vs)
                        (let ((v (set-first vs)))
                          (if (value? v)
                              (let* ((k*^ (alloc state))
                                     (store^ (extend-store k*^
                                               (list-aux-inner-k v k*)
                                               (state-store state))))
                                (list-aux e*
                                  (make-state e* env store^ k*^ (tick state))
                                  wl seen-states))
                              wl))))))
              ; we found a non-continuation at k*, so just ignore it.
              (_ (loop ks wl))))))))

(define make-closure
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define apply-proc
  (lambda (ps as k* state wl seen-states)
    (let loop ((ps ps) (wl wl))
      (if (set-empty? ps)
          wl
          (let ((p (set-first ps)))
            (match p
              (`(closure ,x ,body ,env)
                (let inner-loop ((as as) (wl wl))
                  (if (set-empty? as)
                      (loop (set-rest ps) wl)
                      (inner-loop (set-rest as)
                        (let ((a (set-first as)))
                          (if (value? a)
                              (let* ((loc (alloc state))
                                     (env^ (extend-env x loc env))
                                     (store^ (extend-store loc a
                                               (state-store state))))
                                (add-next-state! wl state seen-states
                                  (make-state body env^ store^ k* (tick state))))
                              wl))))))
              (`(continuation ,k*)
                (let inner-loop ((as as) (wl wl))
                  (if (set-empty? as)
                      (loop (set-rest ps) wl)
                      (inner-loop (set-rest as)
                        (let ((a (set-first as)))
                          (if (value? a)
                              (add-next-state! wl state seen-states
                                (make-state `(quote ,a) (state-env state)
                                  (state-store state) k* (tick state)))
                              wl))))))
              (_ (loop (set-rest ps) wl))))))))

(define add-next-state!
  (lambda (wl state seen-states new-state)
    (if (state-set-includes? new-state (state-next-states state))
        wl
        (cond
          ((state-set-includes? new-state wl)
           (set-state-next-states! state 
             (cons (findf (lambda (x) (state=? x new-state)) wl)
               (state-next-states state)))
           wl)
          ((state-set-includes? new-state seen-states)
           (set-state-next-states! state 
             (cons (findf (lambda (x) (state=? x new-state)) seen-states)
               (state-next-states state)))
           wl)
          (else
            (set-state-next-states! state 
              (cons new-state (state-next-states state)))
            (cons new-state wl))))))

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
(define abs-interp-aux!
  (lambda (wl seen-states)
    (unless (null? wl)
      (let* ((state (car wl))
             (wl (cdr wl))
             (seen-states (cons state seen-states)))
        (printf "abs-interp-aux! exp: ~s\n" (state-exp state))
        (match (state-exp state)
          ((? void? v) (apply-k* state (set v) wl seen-states)) ;; needed to allow apply-k through here.
          ((? number? n) (apply-k* state (set n) wl seen-states))
          ((? boolean? b) (apply-k* state (set b) wl seen-states))
          (`(quote ,d) (apply-k* state (set d) wl seen-states))
          ((? symbol? x)
            (apply-k* state
              (lookup (state-env state) (state-store state) x)
              wl seen-states))
          (`(if ,t ,c ,a)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (if-k c a env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state t env store^ k*^ (tick state)))
                seen-states)))
          (`(zero? ,e)
            (let* ((k*^ (alloc state))
                   (store^ (extend-store k*^
                             (zero?-k (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e (state-env state) store^ k*^ (tick state)))
                seen-states)))
          (`(sub1 ,e)
            (let* ((k*^ (alloc state))
                   (store^ (extend-store k*^
                             (sub1-k (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e (state-env state) store^ k*^ (tick state)))
                seen-states)))
          (`(- ,e1 ,e2)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (subtraction-outer-k e2 env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e1 env store^ k*^ (tick state)))
                seen-states)))
          (`(+ ,e1 ,e2)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (addition-outer-k e2 env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e1 env store^ k*^ (tick state)))
                seen-states)))
          (`(* ,e1 ,e2)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (multiplication-outer-k e2 env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e1 env store^ k*^ (tick state)))
                seen-states)))
          (`(call/cc ,e)
            (let* ((k*^ (alloc state))
                   (store^ (extend-store k*^
                             (call/cc-k (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e (state-env state) store^ k*^ (tick state)))
                seen-states)))
          (`(throw ,cc-e ,v-e)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (throw-k v-e env)
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state cc-e env store^ k*^ (tick state)))
                seen-states)))
          (`(letcc ,x ,body)
            (let* ((loc (alloc state))
                   (k* (state-k* state))
                   (env^ (extend-env x loc (state-env state)))
                   (store^ (extend-store loc
                             (make-continuation k*)
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state body env^ store^ k* (tick state)))
                seen-states)))
          (`(lambda (,x) ,body)
            (apply-k* state (set (make-closure x body (state-env state)))
              wl seen-states))
          (`(set! ,x ,rhs)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (set!-k x env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state rhs env store^ k*^ (tick state)))
                seen-states)))
          (`(begin ,e1 ,e2)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (begin-k e2 env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state e1 env store^ k*^ (tick state)))
                seen-states)))
          (`(list . ,e*) (abs-interp-aux! (list-aux e* state wl seen-states)))
          (`(,rator ,rand)
            (let* ((env (state-env state))
                   (k*^ (alloc state))
                   (store^ (extend-store k*^
                             (application-outer-k rand env (state-k* state))
                             (state-store state))))
              (abs-interp-aux!
                (add-next-state! wl state seen-states
                  (make-state rator env store^ k*^ (tick state)))
                seen-states))))))))

(define list-aux
  (lambda (e* state wl seen-states)
    (if (null? e*)
        (apply-k* state (set '()) wl seen-states)
        (let* ((env (state-env state))
               (k*^ (alloc state))
               (store^ (extend-store k*^
                         (list-aux-outer-k (cdr e*) env (state-k* state))
                         (state-store state))))
          (add-next-state! wl state seen-states
            (make-state (car e*) env k*^ store^ (tick state)))))))

(define abstract-interpret
  (lambda (e)
    ;; setup our default store and k* (cheat a little here since we pass the
    ;; state to the alloc function, but we need the the first allocation to
    ;; bootstrap our state).
    (let* ((k* e)
           (store (extend-store k* empty-k empty-store))
           (initial-state (make-state e empty-env store k* empty-time)))
      (abs-interp-aux! (list initial-state) '())
      initial-state)))

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
  (lambda (state)
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
      (let loop ((wl (list state)) (states '()))
        (if (null? wl)
            (begin
              (display "}")
              (newline)
              (newline)
              (for-each (lambda (state)
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
                          (newline))
                states))
            (let ((s (car wl)) (wl (cdr wl)))
              (pretty-print-state s)
              (let inner-loop ((ns* (state-next-states s)) (wl wl))
                (if (null? ns*)
                    (loop wl (cons s states))
                    (let* ((ns (car ns*))
                            (visited? (visited? ns)))
                      (pretty-print-state ns)
                      (display "  ")
                      (display (state->pretty-name s))
                      (display " -> ")
                      (display (state->pretty-name ns))
                      (display ";")
                      (newline)
                      (inner-loop (cdr ns*)
                        (if visited? wl (cons ns wl))))))))))))

(provide (all-defined-out))
