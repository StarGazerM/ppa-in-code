;; Very Busy Expression Analysis

;; For each program point, which expression *must* be very busy at the expression exit
;; evaluate the expression at the block and store its value for later use (hoisting)

;; Yihao Sun <ysun67@syr.edu>
;; Syracuse 2020

#lang racket

(require "tiny-lang.rkt"
         "flow.rkt")


;; same as Availible Expression
;; kill : Blocks* → AExpr* → P(AExpr*)
(define (kill-VB b s*)
  (define aes (aexpr* s*))
  (list->set
   (match b
     [`(,label = ,(? variable? x) ,(? aexpr? a))
      (filter (λ (ae) (isFreeVar x ae)) aes)]
     [`(,label ,(? bexpr? b)) '()]
     [`(,label SKIP) '()])))

;; all expression are very busy at entry
;; gen : Blocks*  → P(AExpr*)
(define (gen-VB b)
  (list->set
   (match b
     [`(,label = ,(? variable? x) ,(? aexpr? a))
      (aexpr-a a)]
     [`(,label ,(? bexpr? b))
      (aexpr-b b)]
     [`(,label SKIP) '()])))

;; chaos iteration
;; backward must analysis
(define (VB-chaos s*)
  (define lab* (labels s*))
  (define all-ae (aexpr* s*))
  (define flow-setʳ (flowʳ s*))
  ;; chaotic iteration start at AExpr* so at beginning
  (define init-map
    (for/fold ([res (hash)])
              ([l (in-list lab*)])
      (hash-set res l (list->set all-ae))))
  (define (vb-exit entrym exitm l)
    (define ls-prime
      (for/fold ([res '()])
                ([edge flow-setʳ])
        (match edge
          [`(,from ,to)
           (if (equal? to l)
               (cons from res)
               res)])))
    (if (empty? ls-prime)
        (hash-set exitm l (set))
        (hash-set exitm l
                  (apply set-intersect
                         (map (λ (l-prime) (hash-ref entrym l-prime))
                              ls-prime)))))
  (define (vb-entry entrym exitm l)
    (define bl (find-block-by-label s* l))
    (hash-set entrym l
              (set-union (set-subtract (hash-ref exitm l)
                                       (kill-VB bl s*))
                         (gen-VB bl))))
  ;; one iteration
  (define (iter1 entrym exitm)
    (for/fold ([res-entry entrym]
               [res-exit exitm])
              ([l (in-list lab*)])
      (values (vb-entry res-entry res-exit l)
              (vb-exit res-entry res-exit l))))
  ;; iterate until fixpoint
  (define (iter-to-fix entrym exitm)
    (let-values ([(next-entrym next-exitm) (iter1 entrym exitm)])
      (cond
        [(and (equal? next-entrym entrym) (equal? next-exitm exitm))
         (values next-entrym next-exitm)]
        [else
         (iter-to-fix next-entrym next-exitm)])))
  (iter-to-fix init-map init-map))

;; example
(define example2-9
  '(if (1 (> a b))
       ((2 = x (- b a))
        (3 = y (- a b)))
       ((4 = y (- b a))
        (5 = x (- a b)))))

;; very-busy.rkt> (VB-chaos example2-9)
;; (hash
;;  1
;;  (set '(- b a) '(- a b))
;;  2
;;  (set '(- b a) '(- a b))
;;  3
;;  (set '(- a b))
;;  4
;;  (set '(- b a) '(- a b))
;;  5
;;  (set '(- a b)))
;; (hash
;;  1
;;  (set '(- b a) '(- a b))
;;  2
;;  (set '(- a b))
;;  3
;;  (set)
;;  4
;;  (set '(- a b))
;;  5
;;  (set))
