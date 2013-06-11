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

(define empty-k
  (lambda (v/s)
    (car v/s)))

(define eval-exp
  (lambda (exp env s k)
    (match exp
      ((? number? n) (k (answer n s)))
      ((? symbol? x) (k (answer (lookup env s x) s)))
      (`(lambda (,x) ,body)
       (k (answer
            (lambda (a s^ k^)
              (let ((loc (new-loc s^)))
                (let ((env^ (ext-env x loc env)))
                  (let ((s^^ (ext-s loc a s^)))
                    (eval-exp body env^ s^^ k^)))))
            s)))
      ;; AWK: added these three clauses so that I could test the U-cobminator
      ;; AWK: factorial example from oleg's fixed-point article.
      (`(if ,t ,c ,a)
       (eval-exp t env s
         (lambda (v/s^)
           (let ((v (car v/s^)) (s^ (cdr v/s^)))
             (eval-exp (if v c a) env s^ k)))))
      (`(zero? ,e)
       (eval-exp e env s
         (lambda (v/s^)
           (let ((v (car v/s^)) (s^ (cdr v/s^)))
             (k (answer (zero? v) s^))))))
      (`(- ,e1 ,e2)
       (eval-exp e1 env s
         (lambda (v1/s^)
           (let ((v1 (car v1/s^)) (s^ (cdr v1/s^)))
             (eval-exp e2 env s^
               (lambda (v2/s^^)
                 (let ((v2 (car v2/s^^)) (s^^ (cdr v2/s^^)))
                   (k (answer (- v1 v2) s^^)))))))))
      (`(+ ,e1 ,e2)
       (eval-exp e1 env s
         (lambda (v1/s^)
           (let ((v1 (car v1/s^)) (s^ (cdr v1/s^)))
             (eval-exp e2 env s^
               (lambda (v2/s^^)
                 (let ((v2 (car v2/s^^)) (s^^ (cdr v2/s^^)))
                   (k (answer (+ v1 v2) s^^)))))))))
      (`(* ,e1 ,e2)
       (eval-exp e1 env s
         (lambda (v1/s^)
           (let ((v1 (car v1/s^)) (s^ (cdr v1/s^)))
             (eval-exp e2 env s^
               (lambda (v2/s^^)
                 (let ((v2 (car v2/s^^)) (s^^ (cdr v2/s^^)))
                   (k (answer (* v1 v2) s^^)))))))))
      (`(set! ,x ,rhs)
       (eval-exp rhs env s
         (lambda (v/s^)
           (let ((v (car v/s^))
                 (s^ (cdr v/s^)))
             (let ((loc (apply-env env x))) 
               (k (answer (void) (ext-s loc v s^))))))))
      (`(call/cc ,e)
       (eval-exp e env s
         (lambda (p/s^)
           (let ((p (car p/s^)) (s^ (cdr p/s^)))             
             (p (lambda (a s^^ k^) (k (answer a s^^))) s^ k)))))
      (`(begin ,rand1 ,rand2)
       (eval-exp rand1 env s
         (lambda (v1/s^)
           (let ((v1 (car v1/s^))
                 (s^ (cdr v1/s^)))
             (eval-exp rand2 env s^
               (lambda (v2/s^^)
                 (let ((v2 (car v2/s^^))
                       (s^^ (cdr v2/s^^)))
                   (k (answer v2 s^^)))))))))
      (`(,rator ,rand)
       (eval-exp rator env s
         (lambda (p/s^)
           (let ((p (car p/s^))
                 (s^ (cdr p/s^)))
             (eval-exp rand env s^
               (lambda (a/s^^)
                 (let ((a (car a/s^^))
                       (s^^ (cdr a/s^^)))
                   (p a s^^ k)))))))))))

(module* test #f
  (require rackunit)

  (check-eqv?
    (let ((env (ext-env 'a (new-loc empty-s) empty-env))
           (s (ext-s (new-loc empty-s) 7 empty-s)))
      (lookup env s 'a))
    7
    "lookup")

  (check-eqv?
    (eval-exp '5 empty-env empty-s empty-k)
    5
    "cesk-number")

  (check-eqv?
    (eval-exp '(* (+ 3 4) (* (+ 7 8) 6)) empty-env empty-s empty-k)
    (* (+ 3 4) (* (+ 7 8) 6))
     "cesk-arithmetic")

  (check-eqv?
    (eval-exp 'a
      (ext-env 'a (new-loc empty-s) empty-env)
      (ext-s (new-loc empty-s) 7 empty-s)
      empty-k)
    7
     "cesk-variable")

  (check-eqv?
    (eval-exp '((lambda (x) x) 5)
      empty-env
      empty-s
      empty-k)
    5
    "cesk-identity")

  (check-eqv?
    (eval-exp '((lambda (x) (begin (set! x 5) x)) 6)
      empty-env
      empty-s
      empty-k)
    5
     "cesk-set!")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k) 20))
      empty-env
      empty-s
      empty-k)
    20
     "call/cc-1")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k) (k 20)))
      empty-env
      empty-s
      empty-k)
    20
     "call/cc-2")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k)
                          (* 5 4)))
      empty-env
      empty-s
      empty-k)
    (call/cc (lambda (k)
               (* 5 4)))
     "call/cc-3")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k)
                          (k (* 5 4))))
      empty-env
      empty-s
      empty-k)  
    (call/cc (lambda (k)
               (k (* 5 4))))
     "call/cc-4")

  (check-eqv?
    (eval-exp '(call/cc (lambda (k)
                          (* 5 (k 4))))
      empty-env
      empty-s
      empty-k)  
    (call/cc (lambda (k)
               (* 5 (k 4))))
     "call/cc-5")

  (check-eqv?
    (eval-exp '(+ 2 (call/cc (lambda (k)
                               (* 5 (k 4)))))
      empty-env
      empty-s
      empty-k)  
    (+ 2 (call/cc (lambda (k)
                    (* 5 (k 4)))))
     "call/cc-6")

  (check-eqv?
    (eval-exp '(((call/cc (lambda (k) k)) (lambda (x) x)) 1)
      empty-env
      empty-s
      empty-k)  
    (((call/cc (lambda (k) k)) (lambda (x) x)) 1)
     "call/cc-7"))

(provide (all-defined-out))
