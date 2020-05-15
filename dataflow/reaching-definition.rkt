;; Reaching Definition Analysis

;; for each program point, which assignment may been made and not overwritten
;; when program execution reaches this point along some path

;; mainly used to construct direct link between blocks that produce value and
;; blocks that use them.

;; Yihao Sun <ysun67@syr.edu>
;; 2020 Syracuse

#lang racket

;; pure racket way

(require "tiny-lang.rkt"
         "flow.rkt")

;; kill-RD : Blocks* → P(Var* × Lab*&?)

(define (kill-RD b s*)
  (define block* (blocks s*))
  (define (assign-x? b x)
    (match b
      [`(,label = ,(? variable? x1) ,(? aexpr? a))
       (equal? x x1)]
      [else #f]))
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (set-union (list `(,x '?))
                (map (λ (bl)
                       ;; first of a blockis always a label
                       `(,x ,(first bl)))
                     (filter (λ (bl) (assign-x? bl x)) block*)))]
    [`(,label SKIP) '()]
    [`(,label ,(? bexpr? b)) '()]))

(define (gen-RD b s*)
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (list `(,x ,label))]
    [else '()]))

;; similar to availible expression we can use chaotic iteration, but init to ∅
(define (RD-chaos s*)
  (define lab* (labels s*))
  (define flow-set (flow s*))
  (define all-fv (free-vars s*))
  (define init-map
    (for/fold ([res (hash)])
              ([l (in-list lab*)])
      (hash-set res l '())))
  (define (rd-entry entrym exitm l)
    (define ls-prime
      (for/fold ([res '()])
                ([edge flow-set])
        (match edge
          [`(,from ,to)
           (if (equal? to l)
               (cons from res)
               res)])))
    (if (empty? ls-prime)
        (hash-set entrym l
                  (map (λ (v) `(,v '? )) all-fv))
        (hash-set entrym l
                  (apply set-union
                         (map (λ (l-prime) (hash-ref exitm l-prime))
                              ls-prime)))))
  (define (rd-exit entrym exitm l)
    (define bl (find-block-by-label s* l))
    (hash-set exitm l
              (set-union (set-subtract (hash-ref entrym l)
                                       (kill-RD bl s*))
                         (gen-RD bl s*))))
  (define (iter1 entrym exitm)
    (for/fold ([res-entry entrym]
               [res-exit exitm])
              ([l (in-list lab*)])
      (values (rd-entry res-entry res-exit l)
              (rd-exit res-entry res-exit l))))
  (define (iter-to-fix entrym exitm)
    (let-values ([(next-entrym next-exitm) (iter1 entrym exitm)])
      (cond
        [(and (equal? next-entrym entrym) (equal? next-exitm exitm))
         (values next-entrym next-exitm)]
        [else
         (iter-to-fix next-entrym next-exitm)])))
  (iter-to-fix init-map init-map))

;; exmaple 2.7
(define example2-7
  '((1 = x 5)
    (2 = y 1)
    (while (3 (> x 1))
      do
      ((4 = y (* x y))
       (5 = x (- x 1))))))

