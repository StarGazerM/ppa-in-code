;; a distributive framework which can contain basic dataflow analysis
;; using worklist algorithm based on
;; https://www.seas.harvard.edu/courses/cs252/2011sp/slides/Lec02-Dataflow.pdf

;; Yihao Sun
;; Syracsue 2020
#lang racket

(require "tiny-lang.rkt"
         "flow.rkt"
         "avaliable-expression.rkt"
         "reaching-definition.rkt"
         "very-busy.rkt")

;; some fancy renaming to make code more like code in slides
(define ∅? empty?)
(define ∩ set-intersect)
(define ∪ set-union)

;; a distributive analysis framework take a lattice(satisfy decending chain condition)
;; Lattice:
;;   P is target partial order set
;;   ⊓ is meet operator
;;   ⊤ is top
;;   ι is for inital node
;; transfer function:
;;   fₛ
;; I add an extra arg, the current flow graph
(define (distibutive-analysis direction P ⊓ ⊤ ι fₛ graph )
  (define (update-worklist in out w)
    (cond
      [(∅? w)
       (match direction
         ['→ `(In ,in Out ,out)]
         ['← `(In ,out Out ,in)])]
      [else
       (define s (car w))
       (define new-w (cdr w))
       ;; all income flow of s need to meet
       (define out-s-p-list
         (map (λ (l) (hash-ref out l)) (preds graph s)))
       (define in-s
         (if (empty? out-s-p-list)
             ι
             (apply ⊓ out-s-p-list)))
       (define temp (fₛ s in-s))
       (if (not (equal? temp (hash-ref out s)))
           (update-worklist (hash-set in s in-s)
                            (hash-set out s temp)
                            (∪ new-w (succs graph s)))
           (update-worklist (hash-set in s in-s) out new-w))]))
  (define inital-out
    (for/fold ([res (hash)])
              ([s P])
      (hash-set res s ⊤)))
  (define inital-in (hash))
  (update-worklist inital-in inital-out P))

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
  (distibutive-analysis '→ lab* ∩ all-ae (set) fₛ flow-set))

;; test example in PPA
(define example2-5
  '((1 = x (+ a b))
    (2 = y (* a b))
    (while (3 (> y (+ a b)))
      do
      ((4 = a (+ a 1))
       (5 = x (+ a b))))))

;; Reaching Definition
;; Reaching definitions
;;   P = sets of definitions (assignment statements)
;;   Meet operation ⊓ is set union ∪
;;   ⊤ is empty set
(define (RD-framwork s*)
  (define lab* (labels s*))
  (define flow-set (flow s*))
  (define all-fv (free-vars s*))
  (define unknow-assign
    (for/fold ([res (set)])
              ([fv all-fv])
      (set-add res `(,fv '?))))
  (define (fₛ s ins)
    (define b (find-block-by-label s* s))
    (∪ (gen-RD b s*)
       (set-subtract ins (kill-RD b s*))))
  (distibutive-analysis '→ lab* ∪ (set) unknow-assign fₛ flow-set))


;; exmaple 2.7
(define example2-7
  '((1 = x 5)
    (2 = y 1)
    (while (3 (> x 1))
      do
      ((4 = y (* x y))
       (5 = x (- x 1))))))

;; Very Busy Expression
;;   ⊓ is ∩
;;   ⊤ is AExpr
(define (VB-framework s*)
  (define lab* (labels s*))
  (define all-ae (list->set (aexpr* s*)))
  (define flow-setʳ (flowʳ s*))
  (define (fₛ s ins)
    (define b (find-block-by-label s* s))
    (∪ (gen-VB b)
       (set-subtract ins (kill-VB b s*))))
  (distibutive-analysis '← lab* ∩ all-ae (set) fₛ flow-setʳ))


(define example2-9
  '(if (1 (> a b))
       ((2 = x (- b a))
        (3 = y (- a b)))
       ((4 = y (- b a))
        (5 = x (- a b)))))

;; I am lazy for liveness .....
