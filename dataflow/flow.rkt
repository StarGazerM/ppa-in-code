;; data flow graph in intra procedure analysis

#lang racket


(require "tiny-lang.rkt")

(provide (all-defined-out))
;; pure racket version

;; init function return the inital label of a statement
;; get all start point of a flow edge
;; init: Stmt → Lab
(define (init-flow stmt)
  (match stmt
    [`(,label = ,(? variable? x) ,(? aexpr? a)) label]
    [`(,label SKIP) label]
    [`(,(? stmt? stmts) ...) (init-flow (car stmts))]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     label]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     label]))

;; the end of a flow
;; final: Stmt → 𝑷(Lab)
(define (final-flow stmt)
  (match stmt
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (list label)]
    [`(,label SKIP) (list label)]
    ['() '()]
    [`(,(? stmt? s)) (final-flow s)]
    [`(,(? stmt? stmts) ...) (final-flow (cdr stmts))]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (set-union (final-flow s1) (final-flow s2))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (list s)]))

;; flow and reverse flow
;; flow : Stmt -> 𝑷(Lab × Lab)
(define (flow stmt)
  (match stmt
    [`(,label = ,(? variable? x) ,(? aexpr? a)) '()]
    [`(,label SKIP) '()]
    ['() '()]
    [`(,(? stmt? s)) (flow s)]
    [`(,(? stmt? s) ...)
     (define s1 (car s))
     (define s2 (cdr s))
     (set-union (flow s1)
                (flow s2)
                (remove-duplicates
                 (map (λ (l) `(,l ,(init-flow s2))) (final-flow s1))))]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (set-union (flow s1)
                (flow s2)
                `((,label ,(init-flow s1))
                  (,label ,(init-flow s2))))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (set-union (flow s)
                `((,label ,(init-flow s)))
                (map (λ (l) `(,l ,label)) (final-flow s)))]))

;; reverse flow
;; this is easy
(define (flowʳ stmt)
  (map reverse (flow stmt)))


;; immediate predecessor of a statement
;; this not in PPA, but used in Jeff Foster's slides
;; preds :: 𝑷(Lab × Lab) -> Lab -> 𝑷(Lab)
(define (preds graph l)
  (for/fold ([res '()])
            ([edge (in-list graph)])
    (if (equal? (second edge) l)
        (cons (first edge) res)
        res)))

;; immediate succssor of a statement
;; this not in PPA, but used in Jeff Foster's slides
;; succs ::  𝑷(Lab × Lab) -> Lab -> 𝑷(Lab)
(define (succs graph l)
  (for/fold ([res '()])
            ([edge (in-list graph)])
    (if (equal? (first edge) l)
        (cons (second edge) res)
        res)))

;; Example 2.1
(define example2-1
  `((1 = z 1)
    (while (2 (> x 0))
      do
      ((3 = z (* z y))
       (4 = x (- x 1))))))

;; flow.rkt> (flow example2-1)
;; '((1 2) (3 4) (2 3) (4 2))
