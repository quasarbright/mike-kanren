#lang racket

(provide succeed
         fail
         run*
         run
         fresh
         define-relation
         disj
         conj
         conde
         conda
         condu
         ==
         onceo
         alwayso
         nevero)

(module+ test
  (require (except-in rackunit fail)))

; variables
(define (make-var name) (vector name))
(define (var? v) (vector? v))
; examples
(define x-v (make-var 'x))
(define y-v (make-var 'y))

; supported values
(define (value? v) ((or/c var? number? boolean? symbol? (cons/c value?)) v))
(define association? (cons/c var? value?))
(define (substitution? v) ((and/c (listof association?) no-duplicate-cars?) v)) ; and no cycles
(define (no-duplicate-cars? pairs)
  (let loop ([seen-cars '()])
    (match pairs
      ['() #t]
      [(cons pair pairs)
       (or (member (car pair) seen-cars)
           (loop (cons (car pair) seen-cars) pairs))])))


(define empty-sub '())

#; (-> value? substitution? value?)
; looks up variables and follows fusion
(define (walk val sub)
  (let ([association (and (var? val) (assv val sub))])
    (if (pair? association) ; val is a var and lookup succeeded
        (walk (cdr association) sub) ; recursion is necessary in case val is associated to another var
        val)))

(module+ test
  (check-equal? (walk 1 empty-sub) 1)
  (check-equal? (walk x-v `((,x-v . 1))) 1)
  (check-equal? (walk x-v `((,y-v . 1))) x-v)
  (check-equal? (walk x-v `((,y-v . 2) (,x-v . 1))) 1)
  (check-equal? (walk x-v `((,x-v . ,y-v) (,y-v . 1))) 1))

#; (-> var? value? substitution? (or/c #f substitution?))
; extend the substitution with (cons x val) if it would not lead to a cycle, #f otherwise
(define (extend-sub x val sub)
  (cond
    [(occurs? x val sub) #f]
    [else (cons (cons x val) sub)]))

#; (-> var? value? substitution? boolean?)
; does x occur in val?
(define (occurs? x val sub)
  (let ([val (walk val sub)])
    (cond
      [(var? val) (eqv? x val)]
      [(pair? val)
       (or (occurs? x (car val) sub)
           (occurs? x (cdr val) sub))]
      ; atomic
      [else #f])))

(module+ test
  (check-equal? (occurs? x-v x-v empty-sub) #t)
  (check-equal? (occurs? x-v y-v `((,y-v . ,x-v))) #t)
  ; this shouldn't naturally happen
  (check-equal? (occurs? x-v y-v `((,x-v . ,y-v))) #f)
  (check-equal? (occurs? x-v `(1 2 ,x-v) empty-sub) #t)
  (check-equal? (occurs? x-v `(1 2 ,y-v) `((,y-v . ,x-v))) #t)
  (check-equal? (occurs? x-v 1 empty-sub) #f)
  (check-equal? (occurs? x-v y-v empty-sub) #f)
  (check-equal? (occurs? 1 x-v empty-sub) #f)
  (check-equal? (occurs? 1 x-v `((,x-v . 1))) #f))

#; (-> value? value? substitution? substitution?)
; update the substitution to make u and v equal if possible, #f otherwise
(define (unify u v sub)
  (let ([u (walk u sub)]
        [v (walk v sub)])
    (cond
      [(eqv? u v) sub]
      [(var? u) (extend-sub u v sub)]
      [(var? v) (extend-sub v u sub)]
      [(and (cons? u) (cons? v))
       (let ([sub (unify (car u) (car v) sub)])
         (and sub (unify (cdr u) (cdr v) sub)))]
      [else #f])))

(module+ test
  (check-equal? (unify 1 1 empty-sub) empty-sub)
  (check-equal? (unify '(1 2 3) '(1 2 3) empty-sub) empty-sub)
  (check-equal? (unify 1 2 empty-sub) #f)
  (check-equal? (unify '(1 2 3) '(1 2) empty-sub) #f)
  (check-equal? (unify x-v y-v empty-sub) `((,x-v . ,y-v)))
  (check-equal? (unify x-v x-v empty-sub) empty-sub)
  (check-equal? (unify x-v (list 1 y-v) empty-sub) `((,x-v . (1 ,y-v))))
  (check-equal? (unify x-v (list 1 x-v) empty-sub) #f)
  (check-equal? (unify 1 x-v empty-sub) `((,x-v . 1)))
  (check-equal? (unify (list x-v y-v) (list 1 2) empty-sub) `((,y-v . 2) (,x-v . 1)))
  (check-equal? (unify (list 1 2) (list x-v y-v) empty-sub) `((,y-v . 2) (,x-v . 1)))
  (check-equal? (unify (list x-v 2) (list 1 y-v) empty-sub) `((,y-v . 2) (,x-v . 1)))
  ; make sure u and v get walked
  (check-equal? (unify x-v (list 1 2) `((,x-v . (1 2)))) `((,x-v . (1 2))))
  (check-equal? (unify (list 1 2) x-v `((,x-v . (1 2)))) `((,x-v . (1 2))))
  (check-equal? (unify x-v (list 1 2) `((,x-v . ,y-v))) `((,y-v . (1 2)) (,x-v . ,y-v)))
  (check-equal? (unify (list 1 2) x-v `((,x-v . ,y-v))) `((,y-v . (1 2)) (,x-v . ,y-v)))
  (check-equal? (unify x-v (list 1 2) `((,x-v . (1 2 3)))) #f)
  (check-equal? (unify (list 1 2) x-v `((,x-v . (1 2 3)))) #f))

(define (stream? v [element? any/c])
  (or (equal? v '())
      (and (cons? v) (element? (car v)) (stream? (cdr v) element?))
      ((-> (stream-of element?)) v)))
(define ones (cons 1 (λ () ones)))
(define twos (cons 2 (λ () twos)))
(define (nats-from n) (cons n (λ () (nats-from (add1 n)))))
(define nats (nats-from 0))
(define never-stream (λ () never-stream))
(define ((stream-of element/c) v) (stream? v element/c))
(define substitution-stream? (stream-of substitution?))
; a goal succeeds if the stream is non-empty
(define goal? (-> substitution? substitution-stream?))

#; (-> value? value? goal?)
; produce a goal that succeeds when u and v are equal
(define (== u v)
  (lambda (sub)
    (let ([sub (unify u v sub)])
      (if sub (list sub) '()))))

#; goal?
; the simplest successful goal
(define succeed (λ (s) (list s)))

#; goal?
; the simplest failing goal
(define fail (λ (s) '()))

#; (-> goal? goal? goal?)
; interleaves successes of both goals
(define (disj2 g1 g2)
  (lambda (s)
    (append-stream (g1 s) (g2 s))))

#; (-> stream? stream? stream?)
; append the two streams, interleaving suspensions (for bfs behavior)
(define (append-stream s1 s2)
  (cond
    [(null? s1) s2]
    [(cons? s1) (cons (car s1) (append-stream (cdr s1) s2))]
    ; s1 is a suspension, force it and swap for bfs behavior
    ; if you move to promises, don't use lazy bc you only want to force one level at a time
    [else (lambda () (append-stream s2 (s1)))]))

(module+ test
  (check-equal? (append-stream '() '()) '())
  (check-equal? (append-stream '() '(1 2 3)) '(1 2 3))
  (check-equal? (append-stream '(1 2 3) '()) '(1 2 3))
  (check-equal? (append-stream '(1 2 3) '(4 5 6)) '(1 2 3 4 5 6))
  (check-pred procedure? (append-stream (thunk '(1)) '(2)))
  (check-equal? (take-stream #f (append-stream (thunk '(1)) '(2))) '(2 1))
  (check-equal? (take-stream #f (append-stream (thunk '(1)) (thunk '(2)))) '(1 2))
  (check-equal? (take-stream 6 (append-stream ones twos)) '(1 2 1 2 1 2))
  (check-equal? (take-stream 3 (append-stream never-stream ones)) '(1 1 1))
  (check-equal? (take-stream 3 (append-stream ones never-stream)) '(1 1 1))
  (check-equal? (take-stream 4 (append-stream (list* 3 3 never-stream) ones)) '(3 3 1 1)))

#; goal?
; a goal that never succeeds nor fails
(define (nevero)
  (lambda (s)
    (lambda ()
      ((nevero) s))))

#; goal?
; a goal that succeeds infinitely
(define (alwayso)
  (lambda (s)
    (lambda ()
      ((disj2 succeed (alwayso)) s))))

#; (-> (or/c #f natural?) stream? list?)
; return at most the first n elements of the stream as a list or the whole stream if n is false
(define (take-stream n s)
  (cond
    [(null? s) s]
    [(equal? n 0) '()]
    [(cons? s)
     (cons (car s) (take-stream (and n (sub1 n)) (cdr s)))]
    [else (take-stream n (s))]))

(module+ test
  (check-equal? (take-stream 3 '(1 2 3 4)) '(1 2 3))
  (check-equal? (take-stream #f '(1 2 3 4)) '(1 2 3 4))
  (check-equal? (take-stream 2 '()) '())
  (check-equal? (take-stream 0 '(1 2 3)) '())
  (check-equal? (take-stream 0 '()) '())
  (check-equal? (take-stream 5 ones) '(1 1 1 1 1))
  (check-equal? (take-stream 0 never-stream) '())
  (check-equal? (take-stream 3 (thunk '(1 2 3 4))) '(1 2 3))
  (check-equal? (take-stream 3 (thunk (cons 1 (thunk (cons 2 (cons 3 (thunk (error 'boom)))))))) '(1 2 3)))

#; (-> goal? goal? goal?)
; succeeds iff both goals succeed
(define (conj2 g1 g2)
  (lambda (s)
    (append-map-stream g2 (g1 s))))

#; (-> (-> any/c stream?) stream? stream?)
; map a stream-producing function over s and flatten the result from stream-of-streams to stream
(define (append-map-stream f s)
  (cond
    [(null? s) s]
    [(cons? s)
     (append-stream (f (car s)) (append-map-stream f (cdr s)))]
    [else
     (lambda ()
       (append-map-stream f (s)))]))

(module+ test
  (check-equal? (append-map-stream list '(1 2 3)) '(1 2 3))
  (check-equal? (append-map-stream (thunk* (error 'boom)) '()) '())
  (check-equal? (append-map-stream (λ (x) (list x x)) '(1 2 3)) '(1 1 2 2 3 3))
  (check-equal? (take-stream 4 (append-map-stream (λ (x) (list x #f)) ones)) '(1 #f 1 #f))
  (define (repeat x) (thunk (cons x (repeat x))))
  ; don't understand this pattern, but it does seem to interleave
  ; the interaction between the lazy case and appending in the cons case is very subtle. not sure if this is a bug
  (check-equal? (take-stream 15 (append-map-stream repeat (thunk nats))) '(0 0 0 1 0 0 1 0 0 1 0 2 0 1 0)))

#; (-> symbol? (-> var? goal?) goal?)
; call `f` with a fresh variable named `name`
(define (call/fresh name f)
  (let [(var (make-var name))]
    (f var)))

#; (-> value? substitution? value?)
; recursively walk val, diving into pairs
(define (walk* val sub)
  (let ([val (walk val sub)])
    (cond
      [(var? val) val]
      [(cons? val)
       (cons (walk* (car val) sub) (walk* (cdr val) sub))]
      [else val])))

(module+ test
  (check-equal? (walk* 1 empty-sub) 1)
  (check-equal? (walk* x-v empty-sub) x-v)
  (check-equal? (walk* x-v `((,x-v . ,y-v))) y-v)
  (check-equal? (walk* (list x-v) `((,x-v . ,y-v))) (list y-v))
  (check-equal? (walk* `((,x-v ,y-v)) `((,x-v . (,y-v)) (,y-v . 1))) '(((1) 1))))

(define reified-name-substitution? (listof (cons/c var? var?)))

#; (-> natural? symbol?)
; create a reified name using n
(define (reify-name n)
  (string->symbol (string-append "_." (number->string n))))

(module+ test (check-equal? (reify-name 2) '_.2))

#; (-> value? reified-name-substitution? reified-name-substitution?)
; creates a mapping from names to reified names for the value in leftmost-innermost order
(define (reify-sub val [sub empty-sub])
  ; to convert vars to their reified symbols if possible
  (let ([val (walk val sub)])
    (cond
      [(var? val)
       (let* ([n (length sub)]
              [rn (reify-name n)])
         (cons (cons val rn) sub))]
      [(cons? val)
       (let ([sub (reify-sub (car val) sub)])
         (reify-sub (cdr val) sub))]
      [else sub])))

(module+ test
  (check-equal? (reify-sub x-v) `((,x-v . _.0)))
  (check-equal? (reify-sub (list x-v)) `((,x-v . _.0)))
  (check-equal? (reify-sub (list x-v y-v)) `((,y-v . _.1) (,x-v . _.0)))
  (check-equal? (reify-sub (list x-v y-v 1 x-v)) `((,y-v . _.1) (,x-v . _.0)))
  (check-equal? (reify-sub (list x-v 1 (list y-v x-v))) `((,y-v . _.1) (,x-v . _.0))))

#; (-> value? (-> substitution? value?))
; reifies fresh vars in val under sub. curried
(define ((reify val) sub)
  (let* ([val (walk* val  sub)]
         [rsub (reify-sub val)])
    ; this reifies the variables according to the reified name substitution
    (walk* val rsub)))

(module+ test
  (check-equal? ((reify (list x-v 1)) empty-sub) '(_.0 1))
  (check-equal? ((reify (list x-v 1)) `((,x-v . (,y-v ,y-v)))) '((_.0 _.0) 1))
  (check-equal? ((reify (list x-v y-v)) `((,x-v . ,y-v))) '(_.0 _.0))
  (check-equal? ((reify (list x-v y-v)) empty-sub) '(_.0 _.1))
  (check-equal? ((reify (list x-v y-v)) `((,x-v . 1))) '(1 _.0)))

#; (-> (or/c #f natural?) goal? (list-of substitution?))
; get at most the first n substitutions from the goal, or all of them if n is #f
(define (run-goal n g)
  (take-stream n (g empty-sub)))

#; (-> goal? goal? goal? goal?)
; if goal-cond succeeds, run the goal-then. Otherwise, run goal-else
(define (ifte goal-cond goal-then goal-else)
  (λ (sub)
    (let loop ([cond-stream (goal-cond sub)])
      (cond
        [(null? cond-stream) (goal-else sub)]
        [(cons? cond-stream) (append-map goal-then cond-stream)]
        [else
         ; suspend the forcing of the stream to maintain laziness
         (lambda ()
           (loop (cond-stream)))]))))

#; (-> goal? goal?)
; only emit the first success from g
(define (onceo g)
  (lambda (sub)
    (let loop ([stream (g sub)])
      (cond
        [(null? stream) stream]
        [(cons? stream) (list (car stream))]
        [else
         (lambda ()
           (loop (stream)))]))))


;;; macros ;;;

(define-syntax disj
  (syntax-rules ()
    [(disj) fail]
    [(disj g0 g ...) (disj2 g0 (disj g ...))]))

(define-syntax conj
  (syntax-rules ()
    [(conj) succeed]
    [(conj g0 g ...) (conj2 g0 (conj g ...))]))

(define-syntax conde
  (syntax-rules ()
    [(conde (g ...) ...) (disj (conj g ...) ...)]))

(define-syntax conda
  (syntax-rules ()
    [(conda (g g0 ...)) (conj g g0 ...)]
    [(conda (g0 g ...) clause ...)
     ; "ifte"s everything with the first goal of each clause as a condition (like normal cond)
     (ifte g0 (conj g ...) (conda clause ...))]))

(define-syntax condu
  (syntax-rules ()
    [(condu (g0 g ...) ...)
     ; "once"s the first goal of each clause
     (conda ((onceo g0) g ...) ...)]))

(define-syntax fresh
  (syntax-rules ()
    [(fresh () g ...) (conj g ...)]
    [(fresh (x0 x ...) g ...)
     (call/fresh 'x0 (lambda (x0) (fresh (x ...) g ...)))]))

(define-syntax define-relation
  (syntax-rules ()
    [(defrel (name x ...) g ...)
     (define (name x ...)
       (lambda (sub)
         (lambda ()
           ((conj g ...) sub))))]))

(define-syntax run
  (syntax-rules ()
    [(run n (x0 x ...) g ...)
     (run n q (fresh (x0 x ...)
                     (== q (list x0 x ...))
                     g
                     ...))]
    [(run n q g ...)
     (let ([q (make-var 'q)])
       (map (reify q)
            (run-goal n (conj g ...))))]))

(define-syntax run*
  (syntax-rules ()
    [(run* q g ...)
     (run #f q g ...)]))


(module+ test
  (check-equal? (run* q succeed) '(_.0))
  (check-equal? (run* q fail) '())
  (check-equal? (run* q (== q 1)) '(1))
  (check-equal? (run* q (disj (== q 1) (== q 2))) '(1 2))
  (check-equal? (run* q (conj (== q 1) (== q 2))) '())
  (check-equal? (run* q (disj succeed (== q 1))) '(_.0 1))
  (check-equal? (run* q (disj (== q 1) succeed)) '(1 _.0))
  (check-equal? (run* q (conj (== q 1) succeed)) '(1))
  (check-equal? (run* q (conj (== q 1) fail)) '())
  (check-equal? (run* q (disj (== q 1) fail)) '(1))
  (define-relation (nullo l) (== l '()))
  (define-relation (conso a d pair) (== (cons a d) pair))
  (define-relation (appendo xs ys res)
    (conde [(nullo xs) (== ys res)]
           [(fresh (x rest-xs rest+ys)
                   (conso x rest-xs xs)
                   (conso x rest+ys res)
                   (appendo rest-xs ys rest+ys))]))
  (check-equal? (run* q (appendo '() '() q)) '(()))
  (check-equal? (run* q (appendo '() '(1 2 3) q)) '((1 2 3)))
  (check-equal? (run* q (appendo '(1 2 3) '(4 5 6) q)) '((1 2 3 4 5 6)))
  (check-equal? (run* q (appendo q '(4 5 6) '(1 2 3 4 5 6))) '((1 2 3)))
  (check-equal? (run* (xs ys) (appendo xs ys '(1 2 3))) '((() (1 2 3))
                                                          ((1) (2 3))
                                                          ((1 2) (3))
                                                          ((1 2 3) ())))
  (check-equal? (run 1 (a b c) (appendo a b c)) '((() _.0 _.0))))
