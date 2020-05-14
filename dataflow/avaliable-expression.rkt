;; Availible expression
;; for each program point, which expression must have already been computed, and not later modified,
;; on all paths to the program point
;; avoid recomputation of a expression

;; Yihao Sun <ysun67@syr.edu>
;; 2020 Syracuse

#lang racket

(require "tiny-lang.rkt"
         "flow.rkt")

;; pure racket version

;; different from book I put S* in argument, since we are in function programing
;; language, seems we can get rid of this in relational programming style
;; kill : Blocks* → AExpr* → P(AExpr*)
(define (kill-AE b s*)
  (define aes (aexpr* s*))
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (filter (λ (ae) (isFreeVar x ae)) aes)]
    [`(,label ,(? aexpr? b)) '()]
    [`(,label SKIP) '()]))

;; gen : Blocks*  → P(AExpr*)
(define (gen-AE b)
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (filter (λ (ae) (not (isFreeVar x ae))) (aexpr-a a))]
    [`(,label ,(? bexpr? b))
     (aexpr-b b)]
    [`(,label SKIP) '()]))

;; I also put top-level statement
;; AE-entry : Lab* → S* → P(AExp*)
(define (AE-entry s* l)
  (define flow-set (flow s*))
  (define ls-prime
    (for/fold ([res '()])
              ([edge flow-set])
      (match edge
        [`(,from ,to)
         (if (equal? to l)
             (cons from res)
             res)])))
  (for/fold ([res '()])
            ([l-prime ls-prime])
    (set-intersect res (AE-exit l-prime))))

(define (AE-exit s* l)
  (define bl (find-block-by-label s* l))
  (set-union (set-subtract (AE-entry s* l) (kill-AE bl s*))
             (gen-AE bl))
