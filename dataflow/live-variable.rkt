;; live variable analysis

;; For each program point, which variable may be live at the exit from the point
;; apparently, this can be used in dead code elimination

;; Yihao Sun
;; 2020 Syracuse

#lang racket

(require "tiny-lang.rkt"
         "flow.rkt")

(provide (all-defined-out))

;; left hand var will will kill a var
;; kill-LV : Blocks* → P(Var*)
(define (kill-LV b)
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (set x)]
    [`(,label ,(? bexpr? b)) (set)]
    [`(,label SKIP) (set)]))

;; gen all varible in right
;; gen-LV : Blocks* → P(Var*)
(define (gen-LV b)
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (list->set (free-vars a))]
    [`(,label ,(? bexpr? b)) (list->set (free-vars b))]
    [`(,label SKIP) (set)]))

;; entry and exit
(define (LV-chaos s*)
  (define lab* (labels s*))
  (define flow-setʳ (flowʳ s*))
  (define init-map
    (for/fold ([res (hash)])
              ([l (in-list lab*)])
      (hash-set res l (set))))
  (define (lv-exit entrym exitm l)
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
                  (apply set-union
                         (map (λ (l-prime) (hash-ref entrym l-prime))
                              ls-prime)))))
  (define (lv-entry entrym exitm l)
    (define bl (find-block-by-label s* l))
    (hash-set entrym l
              (set-union (set-subtract (hash-ref exitm l)
                                       (kill-LV bl))
                         (gen-LV bl))))
  (define (iter1 entrym exitm)
    (for/fold ([res-entry entrym]
               [res-exit exitm])
              ([l (in-list lab*)])
      (values (lv-entry res-entry res-exit l)
              (lv-exit res-entry res-exit l))))
  (define (iter-to-fix entrym exitm)
    (let-values ([(next-entrym next-exitm) (iter1 entrym exitm)])
      (begin
        (cond
          [(and (equal? next-entrym entrym)
                (equal? next-exitm exitm))
           (values next-entrym next-exitm)]
          [else
           (iter-to-fix next-entrym next-exitm)]))))
  (iter-to-fix init-map init-map))

;;
(define example2-11
  '((1 = x 2)
    (2 = y 4)
    (3 = x 1)
    (if (4 (> y x))
        (5 = z y)
        (6 = z (* y y)))
    (7 = x z)))

;; live-variable.rkt> (LV-chaos example2-11)
;; (hash
;;  1
;;  (set)
;;  2
;;  (set)
;;  3
;;  (set 'y)
;;  4
;;  (set 'x 'y)
;;  5
;;  (set 'y)
;;  6
;;  (set 'y)
;;  7
;;  (set 'z))
;; (hash
;;  1
;;  (set)
;;  2
;;  (set 'y)
;;  3
;;  (set 'x 'y)
;;  4
;;  (set 'y)
;;  5
;;  (set 'z)
;;  6
;;  (set 'z)
;;  7
;;  (set))
