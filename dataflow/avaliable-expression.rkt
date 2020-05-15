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

;;HERE>>>>>>>>>>>>>>>>>>>>>>>>>>>
(define (kill-AE b s*)
  (define aes (aexpr* s*))
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (filter (λ (ae) (isFreeVar x ae)) aes)]
    [`(,label ,(? bexpr? b)) '()]
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
;; AE-entry : Lab* → S*  → P(AExp*)
;; in PPA book it is written in normal recursion style this will not work actually, since
;; what we want to perform is "chaotic iteration", one way to is using tail call version
;; to pass the whole result through each interation and stop when a fixpoint is reached

;; not working
(define (AE-entry s* l )
  (define flow-set (flow s*))
  (define ls-prime
    (for/fold ([res '()])
              ([edge flow-set])
      (match edge
        [`(,from ,to)
         (if (equal? to l)
             (cons from res)
             res)])))
  (displayln ls-prime)
  (if (empty? ls-prime)
      '()
      (apply set-intersect
             (map (λ (l-prime) (AE-exit s* l-prime)) ls-prime))))

(define (AE-exit s* l)
  (define bl (find-block-by-label s* l))
  (set-union (set-subtract (AE-entry s* l) (kill-AE bl s*))
             (gen-AE bl)))

;; choas iteration version
(define (AE-chaos s*)
  (define lab* (labels s*))
  (define all-ae (aexpr* s*))
  (define flow-set (flow s*))
  ;; chaotic iteration start at AExpr* so at beginning
  (define init-map
    (for/fold ([res (hash)])
              ([l (in-list lab*)])
      (hash-set res l all-ae)))
  ;; ae-entry & ae-exit will return new entry/exit map
  (define (ae-entry entrym exitm l)
    (define ls-prime
      (for/fold ([res '()])
                ([edge flow-set])
        (match edge
          [`(,from ,to)
           (if (equal? to l)
               (cons from res)
               res)])))
    (if (empty? ls-prime)
        (hash-set entrym l '())
        (hash-set entrym l
                  (apply set-intersect
                         (map (λ (l-prime) (hash-ref exitm l-prime))
                              ls-prime)))))
  (define (ae-exit entrym exitm l)
    (define bl (find-block-by-label s* l))
    (hash-set exitm l
              (set-union (set-subtract (hash-ref entrym l)
                                       (kill-AE bl s*))
                         (gen-AE bl))))
  ;; one iteration
  (define (iter1 entrym exitm)
    (for/fold ([res-entry entrym]
               [res-exit exitm])
              ([l (in-list lab*)])
      (values (ae-entry res-entry res-exit l)
              (ae-exit res-entry res-exit l))))
  ;; iterate until fixpoint
  (define (iter-to-fix entrym exitm)
    (let-values ([(next-entrym next-exitm) (iter1 entrym exitm)])
      (cond
        [(and (equal? next-entrym entrym) (equal? next-exitm exitm))
         (values next-entrym next-exitm)]
        [else
         ;; (displayln "entry")
         ;; (pretty-display next-entrym)
         ;; (displayln "exit")
         ;; (pretty-display next-exitm)
         ;; (displayln ">>>>>>>>>")
         (iter-to-fix next-entrym next-exitm)])))
  (iter-to-fix init-map init-map))

;;

(define example2-5
  '((1 = x (+ a b))
    (2 = y (* a b))
    (while (3 (> y (+ a b)))
      do
      ((4 = a (+ a 1))
       (5 = x (+ a b))))))

;; avaliable-expression.rkt> (AE-chaos example2-5)
;; '#hash((1 . ())
;;        (2 . ((+ a b)))
;;        (3 . ((+ a b)))
;;        (4 . ((+ a b)))
;;        (5 . ()))
;; '#hash((1 . ((+ a b)))
;;        (2 . ((* a b) (+ a b)))
;;        (3 . ((+ a b)))
;;        (4 . ())
;;        (5 . ((+ a b))))
;; avaliable-expression.rkt> 
