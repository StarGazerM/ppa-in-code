;; a distributive framework which can contain basic dataflow analysis
;; using worklist algorithm based on
;; https://www.seas.harvard.edu/courses/cs252/2011sp/slides/Lec02-Dataflow.pdf

;; Yihao Sun
;; Syracsue 2020
#lang racket

(require "tiny-lang.rkt"
         "flow.rkt"
         "avaliable-expression.rkt")

;; some fancy renaming to make code more like code in slides
(define ∅? empty?)
(define ∩ set-intersect)
(define ∪ set-union)

;; a distributive analysis framework take a lattice(satisfy decending chain condition)
;; Lattice:
;;   P is target partial order set
;;   ⊓ is meet operator
;;   ⊤ is top
;; transfer function:
;;   fₛ
;; I add an extra arg, the current flow graph
(define (distibutive-analysis P ⊓ ⊤ fₛ graph)
  (define (update-worklist out w)
    (cond
      [(∅? w) out]
      [else
       (define s (car w))
       (displayln s)
       (define new-w (cdr w))
       ;; all income flow of s need to meet
       (define out-s-p-list
         (map (λ (l) (hash-ref out l)) (preds graph s)))
       (define temp
         (if (empty? out-s-p-list)
             (fₛ s (set))
             (fₛ s (apply ⊓ out-s-p-list))))
       ;; seems here ∪ is append?
       (if (not (equal? temp (hash-ref out s)))
           (update-worklist (hash-set out s temp)
                            (append new-w (succs graph s)))
           (update-worklist out new-w))]))
  (define inital-out
    (for/fold ([res (hash)])
              ([s P])
      (hash-set res s ⊤)))
  (update-worklist inital-out P))

;; let's test using framework to make a avaliable expression, which is forward must
;; Available expressions
;;   P = sets of expressions
;;   Meet operation ⊓ is set intersection ∩
;;   ⊤ is set of all expressions
(define (AE-framework s*)
  (define lab* (labels s*))
  (define all-ae (list->set (aexpr* s*)))
  (define flow-set (flow s*))
  (define (fₛ s ins)
    (define b (find-block-by-label s* s))
    (∪ (gen-AE b)
       (set-subtract ins (kill-AE b s*))))
  (distibutive-analysis lab* ∩ all-ae fₛ flow-set))



;; test example in PPA
(define example2-5
  '((1 = x (+ a b))
    (2 = y (* a b))
    (while (3 (> y (+ a b)))
      do
      ((4 = a (+ a 1))
       (5 = x (+ a b))))))
