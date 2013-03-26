(library (cesk-quines-simple)
  (export evalo eval-expo empty-env empty-store empty-k)
  (import (rnrs) (mk-lib) (lookupo-lib))

  (define answer
    (lambda (v s)
      (cons v s)))

  (define not-in-envo
    (lambda (x env)
      (fresh (x*)
        (symbolo x)
        (env->x*o env x*)
        (absento x x*))))

  (define not-in-storeo
    (lambda (addr store)
      (fresh (addr*)
        (numbero addr)
        (store->addr*o store addr*)
        (absento addr addr*))))

  (define make-proc
    (lambda (x body env)
      `(closure ,x ,body ,env)))
  
  (define apply-proco
    (lambda (p a s^ k^ out)
      (fresh (x body env addr env^ s^^)
        (== (make-proc x body env) p)
        (ext-envo x addr env env^)
        (ext-storeo addr a s^ s^^)
        (numbero addr)
        (symbolo x)
        (not-in-storeo addr s^) ; not-in-storeo also calls numbero on addr--is this redundancy desireable?
        (eval-exp-auxo body env^ s^^ k^ out)
        )))

  (define apply-ko
    (lambda (k^ v/s out)
      (conde
        [(fresh (v s)
           (== empty-k k^)
           (== v/s out)
           (== (answer v s) v/s))
         ]
        [(fresh (p k a s^^)
           (== (application-inner-k p k) k^)
           (== (answer a s^^) v/s)
           (apply-proco p a s^^ k out)
           )]
        [(fresh (rand env k p s^)
           (== (application-outer-k rand env k) k^)
           (== (answer p s^) v/s)
           (eval-exp-auxo rand env s^ (application-inner-k p k) out)
           )]
        [(fresh (v k v* s^^ ans)
           (== (list-aux-inner-k v k) k^)
           (== (answer v* s^^) v/s)
           (== (answer (cons v v*) s^^) ans)
           (apply-ko k ans out))]
        [(fresh (e* env k v s^ e*-rest ignore)
           (== (list-aux-outer-k e* env k) k^)
           (== (answer v s^) v/s)
           (== `(,ignore . ,e*-rest) e*)
           (list-auxo e*-rest env s^ (list-aux-inner-k v k) out)
           )])))

  (define empty-k '(empty-k))

  (define application-inner-k
    (lambda (p k)
      `(application-inner-k ,p ,k)))

  (define application-outer-k
    (lambda (rand env k)
      `(application-outer-k ,rand ,env ,k)))

  (define list-aux-inner-k
    (lambda (v k)
      `(list-aux-inner-k ,v ,k)))

  (define list-aux-outer-k
    (lambda (e* env k)
      `(list-aux-outer-k ,e* ,env ,k)))

  (define eval-exp-auxo
    (lambda (exp env s k out)
      (conde
        [(fresh (datum ans)
           (== `(quote ,datum) exp)
           (== (answer datum s) ans)
           (absento 'closure datum)
           (not-in-envo 'quote env)
           (apply-ko k ans out))]
        [(fresh (x body ans)
           (== `(lambda (,x) ,body) exp)
           (== (answer (make-proc x body env) s) ans)
           (not-in-envo 'lambda env)
           (symbolo x) ; interesting: adding this symbolo constraint increased the runtime by ~7%
           (apply-ko k ans out))]
        [(fresh (v ans)
           (symbolo exp)
           (== (answer v s) ans)
           (lookupo exp env s v)
           (apply-ko k ans out))]
        [(fresh (rator rand)
           (== `(,rator ,rand) exp)
           (eval-exp-auxo rator env s (application-outer-k rand env k) out)
           )]
        [(fresh (e*)
           (== `(list . ,e*) exp)
           (not-in-envo 'list env)
           (list-auxo e* env s k out)
           )])))

  (define list-auxo
    (lambda (e* env s k out)
      (conde
        [(fresh (ans)
           (== '() e*)
           (== (answer '() s) ans)
           (apply-ko k ans out))]
        [(fresh (e ignore ignore^)
           (== `(,e . ,ignore) e*)
           (eval-exp-auxo e env s (list-aux-outer-k e* env k) out))])))

  (define eval-expo
    (lambda (exp env s k out)
      (fresh (ans s^)
        (== (answer out s^) ans)
        (eval-exp-auxo exp env s k ans))))

  (define evalo
    (lambda (exp out)
      (eval-expo exp empty-env empty-store empty-k out)))

  )