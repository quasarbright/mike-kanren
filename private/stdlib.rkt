#lang racket

(require "../main.rkt")

(provide conso
         caro
         cdro
         nullo
         listo)

; --- pairs and lists ---

(define-relation (conso a d pair)
  (== (cons a d) pair))

(define-relation (caro a pair)
  (fresh (d)
         (conso a d pair)))

(define-relation (cdro d pair)
  (fresh (a)
         (conso a d pair)))

(define-relation (nullo v)
  (== v '()))

(define-relation (listo l)
  (conde
   [(nullo l)]
   [(fresh (a d) (conso a d l) (listo d))]))

