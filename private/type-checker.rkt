#lang racket
; a type checker written in mini kanren
(require "../main.rkt"
         "./stdlib.rkt")
(module+ test (require rackunit))

; simply typed lambda calculus
; no type schemes for now

#|
<expr> := (λ <symbol> <expr>)
       | (<expr> <expr>)
       | <symbol>
<type> := (-> <type> <type>)
<env> := '() | (cons (list <symbol> <type>) <env>)
|#

; type check relation
; under `env`, `expr` can be assigned type `type`
(define-relation (:o-env env expr type)
  (conde
   ; var
   [(lookupo env expr type)]
   ; abs
   [(fresh (argname body t-arg env-body t-body)
           ; this assumes argname is a symbol
           ; constraints would be useful here
           (== expr (list 'λ argname body))
           (extendo env argname t-arg env-body)
           (== type (list '-> t-arg t-body))
           (:o-env env-body body t-body))]
   ; app
   [(fresh (rator rand t-arg t-ret)
           (== expr (list rator rand))
           (== type t-ret)
           (:o-env env rator (list '-> t-arg t-ret))
           (:o-env env rand t-arg))]))

(define-relation (:o expr type)
  (:o-env empty-env expr type))

(define empty-env '())

; succeeds when (list varname type) is a member of env
; only succeeds on the first match to respect scoping
(define-relation (lookupo env varname type)
  (onceo (conde
          [(caro (list varname type) env)]
          ; for '((x t1) (x t2)) lookupo will succeed twice. should only get the first one
          ; that's why I use once
          [(fresh (rest-env) (cdro rest-env env) (lookupo rest-env varname type))])))

; extends env with (varname : type) to extended-env
(define-relation (extendo env varname type extended-env)
  (conso (list varname type) env extended-env))

(module+ test
  ; type inference
  (check-equal? (run* t (:o '(λ x x) t)) '((-> _.0 _.0)))
  (check-equal? (run* t (:o '(λ x (λ y x)) t)) '((-> _.0 (-> _.1 _.0))))
  ; type-driven program synthesis
  ; would benefit from constraints
  (check-equal? (run 1 expr (fresh (t) (:o expr (list '-> t t)))) '((λ _.0 _.0))))
