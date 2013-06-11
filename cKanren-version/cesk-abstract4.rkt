#lang cKanren

(require (except-in cKanren/miniKanren fail))
(require cKanren/absento)
(require cKanren/neq)

(require (only-in racket remove-duplicates))

;; state creation/teardown
(define stateo
  (lambda (exp env store k* time state)
    (== `(state ,exp ,store ,k* ,time) state)))

;; environment management
(define empty-envo '(() . ()))

(define extend-envo
  (lambda (x loc env env^)
    (fresh (x* loc*)
      (symbolo x)
      (== `(,x* . ,loc*) env)
      (== env^ `((,x . ,x*) (,loc . ,loc*))))))

(define apply-env-helpo
  (lambda (x x* loc* loc)
    (conde
      [(== '() x*) (== #f #t)]
      [(fresh (var x*^ var-loc loc*^)
         (symbolo var)
         (symbolo x)
         ; DANGER: no longer have numbers to represent locations these are now
         ;         concrete lists of some length of some sort of symbols.
         ; (numbero loc)
         ; (numbero var-loc)
         (== `(,var . ,x*^) x*)
         (== `(,var-loc . ,loc*^) loc*)
         (conde
           [(== var x) (== loc var-loc)]
           [(=/= var x) (apply-env-helpo x x*^ loc*^ loc)]))])))

(define apply-envo
  (lambda (env x loc)
    (fresh (x* loc*)
      (== env `(,x* . ,loc*))
      (apply-env-helpo x x* loc* loc))))

;; store management.  locations are now represented a lists of symbols (or
;; logic vars restricted to be symbols).
(define empty-store '(() . ()))

;; POSSIBLE DANGER: we play the absento game in the first conde clause of the
;;                  caller, but that doesn't guarantee that we are absent in
;;                  this clause.  it seems like there might be the standard
;;                  problems with a length instantiated data structure.
(define extend-store-helpero
  (lambda (loc val loc* vals* store^)
    (conde
      [(== store^ empty-store) (== #f #t)] ;; fail if we cannot find it
      [(fresh (loc-fst val-fst loc*^ vals*^)
         (== `(,loc-fst . ,loc*^) loc*)
         (== `(,vals-fst . ,vals*^) vals*)
         (conde
           [(== loc loc-fst)
             (fresh (vals^)
               (== `(,val . ,vals-fst) vals^) ; should be set-add
               (== `(,loc* . (,vals^ . ,vals*^)) store^))]
           [(=/= loc loc-fst)
             (== `(,loc*^^ . ,vals*^^) store^^)
             (== `((,loc-fst . ,loc*^^) . (,vals-fst . ,vals*^^)) store^)
             (extend-store-helpero loc val loc*^ vals*^ store^^)]))])))

;; DANGER: we're using absento here, but our loc is 1) a data structure and 2)
;;         when running in reverse may not be ground.
(define not-in-storeo
  (lambda (loc loc*)
    (absento loc loc*)))

;; DANGER: we're representing the values in store as a list, but we really want
;;         to use a set here, but is the clp-set up to the task?
(define extend-storeo
  (lambda (loc val store store^)
    (fresh (loc* vals*)
      (== `(,loc* . ,vals*))
      (conde
        [(not-in-storeo loc loc*)
         (fresh (vals)
           (== vals `(,val)) ;; should be a set
           (== `((,loc . ,loc*) . (,vals . ,vals*)) store^))]
        [(extend-store-helpero loc val loc* vals* store^)]))))

(define apply-store-helpero

(define apply-storeo
  (lambda (store loc vals)
    (fresh (loc* vals*)
      (== `(,loc* . ,vals*) store)
      (apply-store-helpero loc loc* vals* vals))))

(define apply-store-helpero
  (lambda (loc loc* vals* vals)
    (conde
      [(== store empty-store) (== #t #f)]
      [(fresh (loc-fst loc*^ vals-fst vals*^)
         (== `(,loc-fst . ,loc*^) loc*)
         (== `(,vals-fst . ,vals*^) vals*)
         (conde
           [(== loc loc-fst) (== vals-fst vals)]
           [(=/= loc loc-fst)
            (apply-store-helpero loc loc*^ vals*^ vals)]))])))

(define alloc
  (lambda (state loc)
    (fresh (exp env store k* time exp-label exp-body)
      (stateo exp env store k* time state)
      (== `(,exp-label . ,exp-body) exp)
      (== `(,time . ,exp-label) loc))))

(define lookupo
  (lambda (env store x vals)
    (fresh (loc)
      (apply-envo env x loc)
      (apply-storeo store loc vals))))

(define empty-time '())

;; DANGER: ticko implements a 1CFA style tick, but if this is extended it means
;;         that the tick will be a fixed-length list, that may be equal to or
;;         less than the total length.
(define ticko
  (lambda (state time^)
    (fresh (exp env store k* time exp-label exp-body)
      (stateo exp env store k* time)
      (== `(,exp-label . ,exp-body) exp)
      (== `(,exp-label) time^)
      ;; example of 2CFA (yikes!)
      #;(conde
          [(== time empty-time)
           (== `(,exp-label) time^)]
          [(fresh (time1)
             (== `(,time1) time)
             (== `(,exp-label ,time1) time^))]
          [(fresh (time1 time2)
             (== `(,time1 ,time2) time)
             (== `(,exp-label ,time1) time^))])))

(define empty-ko
  (lambda (k^)
    (== '(empty-k) k^)))

(define if-ko
  (lambda (c a env k* k^)
    (== `(if-k ,c ,a ,env ,k*) k^)))

(define call/cc-k
  (lambda (k* k^)
    (== `(call/cc-k ,k*) k^)))

(define throw-k
  (lambda (v-e env k^)
    (== `(throw-k ,v-e ,env) k^)))

(define set!-ko
  (lambda (x env k* k^)
    (== `(set!-k ,x ,env ,k*) k^)))

(define begin-ko
  (lambda (e2 env k* k^)
    (== `(begin-k ,e2 ,env ,k*) k^)))

(define application-inner-ko
  (lambda (p* k* k^)
    (== `(application-inner-k ,p* ,k*) k^)))

(define application-outer-ko
  (lambda (rand env k* k^)
    (== `(application-outer-k ,rand ,env ,k*) k^)))

(define list-aux-inner-ko
  (lambda (loc k* k^)
    (== `(list-aux-inner-k ,loc ,k*) k^)))

(define list-aux-outer-ko
  (lambda (e* env k* k^)
    (== `(list-aux-outer-k ,e* ,env ,k*) k^)))

(define continuationo
  (lambda (k* cc)
    (== `(continuation ,k*) cc)))

;; my stab at trying to separate out continuations in the store from values in the store
(define not-ko
  (lambda (x)
    (conde
      [(== (void) x)]
      [(fresh (var body env) (closureo var body env x))]
      ;; other concrete types here
      [(fresh (kw rest)
         (== `(,kw . ,rest) k)
         (absento kw '(empty-k call/cc-k set!-k application-inner-k
                       application-outer-k)))])))

(define valueo not-ko)

(define not-valueo
  (lambda (x)
    (fresh (kw rest)
      (== `(,kw . ,rest) k)
      (conde
        [(== kw 'empty-k)]
        [(== kw 'call/cc-k)]
        [(== kw 'set!-k)]
        [(== kw 'application-inner-k)]
        [(== kw 'application-outer-k)]))))

(define ko not-valueo)

(define set!-k-helpero
  (lambda (vs loc env k* state wl seen-states state-adjaceny wl^ state-adjacency^)
    (conde
      [(== vs '())
       (== wl wl^)
       (== state-adjacency state-adjacency^)]
      [(fresh (v vs^)
         (== `(,v . ,vs^) vs)
         (conde
           [(valueo v)
            (fresh (exp env store k* time store^ time^ state^ wl^^ state-adjacency^^)
              (stateo exp env store k* time state)
              (extend-store loc v store store^)
              (stateo '(quote ,(void)) env store^ k* time^)
              (add-next-state wl state seen-states state-adjacency state^ wl^^ state-adjacency^^)
              (set!-k-helpero vs^ loc env k* state wl^^
                seen-states state-adjacency^^ wl^ state-adjacency^))]
           [(not-valueo v)
            (set!-k-helpero vs^ loc env k* state wl
              seen-states state-adjacency wl^ state-adjacency^)]))])))

(define apply-k*-helpero
  (lambda (ks state seen-states wl state-adjacency wl^ state-adjacency^)
    (conde
      [(== ks '()) ; should be set empty check
       (== wl wl^)
       (== state-adjacency state-adjacency^)]
      [(fresh (k ks^)
         (== `(,k . ,ks^) ks)
         (conde
           [(empty-ko k)
            (apply-k*-helpero ks^ state seen-states wl
              state-adjacency wl^ state-adjacency^)]
           [(fresh (k* cc as)
              (call/cc-k k* k^)
              ; normally we would use a set here
              (continuationo k* cc)
              (== `(,cc) as)
              (apply-proco vs as k* state wl
                seen-states state-adjacency wl^ state-adjacency^))]
           [(fresh (x env k* loc)
              (set!-ko x env k* k)
              (apply-env env x loc)
              (set!-k-helpero vs loc env k* state wl
                seen-states state-adjacency wl^ state-adjacency^))]
           [(fresh (p* k*)
              (application-inner-ko p* k* k^)
              (apply-proco p* vs k* state wl seen-states state-adjacency wl^ state-adjacency^))]
           [(fresh (rand env k* exp env store k* time store^ state^ k*^ time^)
              (application-outer-ko rand env k* k)
              (stateo exp env store k* time state)
              (alloc state k*^)
              (application-inner-k vs k* k^)
              (extend-store k*^ k^ store store^)
              (ticko state time^)
              (stateo rand env store^ k*^ time^ state^)
              (add-next-stateo wl state seen-states state-adjacency state^ wl^ state-adjacency^))]
           [(not-ko k)
            (apply-k*-helpero ks^ state seen-states wl
              state-adjacency wl^ state-adjacency^)]))])))

(define apply-k*
  (lambda (state vs wl seen-states state-adjacency wl^ state-adjacency^)
    (fresh (exp env store k* time ks)
      (stateo exp env store k* time state)
      (apply-storeo store k* ks)
      (apply-k*-helpero ks state seen-states wl state-adjacency wl^ state-adjacency^))))

(define closureo
  (lambda (x body env clos)
    (== `(closure ,x ,body ,env) clos)))

(define not-appliable
  (lambda (x)
    (fresh (kw rest)
      (== `(,kw . ,rest) x)
      (absento kw '(closure continuation)))))

(define apply-proco
  (lambda (ps as k* state wl seen-states state-adjacency wl^ state-adjacency^)
    (conde
      [(== ps '()) (== wl wl^) (== state-adjacency state-adjacency^)]
      [(fresh (p ps^)
         (== `(,p . ,ps^) ps)
         (conde
           [(fresh (x body env)
              (closureo x body env p)
              (




