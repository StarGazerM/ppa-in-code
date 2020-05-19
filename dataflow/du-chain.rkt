;; Define-Use chains

;; link the label to where use it

;; Yihao Sun <ysun67@syr.edu>
;; 2020 Syracuse

#lang racket

(require "tiny-lang.rkt"
         "flow.rkt"
         "live-variable.rkt")

;; find all path from  src to dst
(define (find-all-path s* src dst)
  (define flow-set (flow s*))
  (define (next-label lc)
    (for/fold ([res '()])
              ([edge (in-list flow-set)])
      (if (equal? (first edge) lc)
          (cons (second edge) res)
          res)))
  (define (helper l pre)
    (define nexts (next-label l))
    (cond
      [(equal? l dst) `(,(reverse (cons dst pre)))]
      [(empty? nexts) '()]
      [else
       (apply append
              (map (λ (n) (helper n (cons l pre)))
                   nexts))]))
  (helper src '()))

;; definition clear path of a varible is the dataflow path do not contain assignment to that variable
(define (clear-path? s* x l l-p)
  (define paths (find-all-path s* l l-p))
  (cond
    [(empty? paths) #f]
    [(use? s* x l-p)
     (andmap (λ (p)
               (andmap (λ (li) (not (def? s* x li)))
                       (take p (sub1 (length p)))))
             paths)]
    [else #f]))

;; originally only take x and l
(define (use? s* x l)
  (define bl (find-block-by-label s* l))
  (member x (set->list (gen-LV bl))))

(define (def? s* x l)
  (define bl (find-block-by-label s* l))
  (member x (set->list (kill-LV bl))))

;; ud,du : Var* × Lab* → P(Lab*)
(define (ud s* x l-p)
  (define all-lab (labels s*))
  (define l-set
    (filter (λ (l)
              (let ([l-pps
                     (for/fold ([res '()])
                               ([edge (in-list (flow s*))])
                       (if (equal? (first edge) l)
                           (cons (second edge) res)
                           res))])
                (and (def? s* x l)
                     (ormap (λ (l-pp) (clear-path? s* x l-pp l-p)) l-pps))))
            all-lab))
  ;; if x is not defined inside current S* but not modified in S*
  (if (clear-path? s* x (init-flow s*) l-p)
      (set-add l-set '?)
      l-set))

#;(define (du s* x l)
  (define flow-set (flow s*))
  (define all-lab (labels s*))
  (define l-pps
    (for/fold ([res '()])
              ([edge (in-list (flow s*))])
      (if (equal? (first edge) l)
          (cons (second edge) res)
          res)))
  (cond
    [(equal? l '?)
     (filter (λ (l-p) (clear-path? s* x (init-flow s*) l-p)) all-lab)]
    [(not (def? s* x l)) '()]
    [else
     (filter (λ ()
               )
             all-lab)]))

(define (du s* x l)
  (define flow-set (flow s*))
  (define all-lab (labels s*))
  (for/fold ([res '()])
            ([l-p (in-list all-lab)])
    (set-union res (ud s* x l-p))))

;; in this example block 1 can be removed since it no used before reassign
;; code motion can be performed on block 6
(define example2-12
  '((1 = x 0)
    (2 = x 3)
    (if (3 (== z x))
        (4 = z 0)
        (5 = z x))
    (6 = y x)
    (7 = x (+ y z))))

;; du-chain.rkt> (ud example2-12 'z 3)
;; '(?)
;; du-chain.rkt> (ud example2-12 'z 4)
;; '()
;; du-chain.rkt> (ud example2-12 'z 7)
;; '(4 5)
;; du-chain.rkt> (ud example2-12 'y 1)
;; '()
;; du-chain.rkt> (ud example2-12 'y 7)
;; '(6)
;; du-chain.rkt> (ud example2-12 'x 3)
;; '(2)
;; du-chain.rkt> (ud example2-12 'x 5)
;; '(2)
;; du-chain.rkt> (ud example2-12 'x 6)
;; '(2)
;; du-chain.rkt> 
